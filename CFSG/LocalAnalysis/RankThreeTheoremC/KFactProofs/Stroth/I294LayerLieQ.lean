module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Defs
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

private theorem lieIndexChar_eq_characteristic' (d : TauCeti.LieTypeIndex) :
    CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar d = d.characteristic := by
  cases d <;> simp [CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar]

private theorem isChevIndexOfChar_of_lieIndexChar' {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar d = p) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsChevIndexOfChar p d := by
  cases d with
  | A r q =>
    match r with
    | 0 => exact h
    | 1 => exact Or.inl h
    | r + 2 => exact h
  | twistedA r q =>
    match r with
    | 0 => exact h
    | 1 => exact h
    | 2 => exact Or.inl h
    | r + 3 => exact h
  | _ => exact h

theorem isChevOfChar_of_characteristic {L : Type} [Group L] {d : TauCeti.ValidLieTypeIndex}
    {p : ℕ} (hd : d.1.characteristic = p) (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar p L :=
  ⟨d, isChevIndexOfChar_of_lieIndexChar' (by rw [lieIndexChar_eq_characteristic', hd]), ⟨e⟩⟩

private theorem comp_le_or_commute_aux {M : Type*} [Group M] [Finite M] {B H K : Subgroup M}
    (hB : CFSG.Assembly.IsComponentOf B H) (hKH : K ≤ H)
    (hK : H ≤ Subgroup.normalizer (K : Set M)) : B ≤ K ∨ ⁅B, K⁆ = ⊥ := by
  have hBH := hB.1
  have hc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hBH).1 hB
  have hKn : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hK
  rcases CFSG.LocalCores.component_normal_subgroup hc hKn with h | h
  · left
    intro x hx
    have hx' : (⟨x, hBH hx⟩ : H) ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
    exact Subgroup.mem_subgroupOf.1 (h hx')
  · right
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    have hx' : (⟨x, hBH hx⟩ : H) ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
    have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h) hx'
    rw [Subgroup.mem_centralizer_iff] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (⟨y, hKH hy⟩ : H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.2 hy
    exact congrArg Subtype.val (h1 ⟨y, hKH hy⟩ hy')

section Constrained

variable {Y : Type} [Group Y] [Finite Y]

private theorem pow_eq_one_of_mem_pCoreOf {p : ℕ} {N : Subgroup Y} {x : Y}
    (hx : x ∈ CFSG.Open.pCoreOf p N) : ∃ k : ℕ, x ^ p ^ k = 1 := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥N) ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have h2 : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  simpa using congrArg N.subtype h2

private theorem conj_mem_pCoreOf {p : ℕ} {N : Subgroup Y} {n x : Y} (hn : n ∈ N)
    (hx : x ∈ CFSG.Open.pCoreOf p N) : n * x * n⁻¹ ∈ CFSG.Open.pCoreOf p N := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨(⟨n, hn⟩ : ↥N) * y * (⟨n, hn⟩ : ↥N)⁻¹,
    (CFSG.pCore_normal (p := p) (G := ↥N)).conj_mem y hy _, ?_⟩
  simp

theorem glaPPrimeCoreOf_eq_bot_of_constrained {p : ℕ} (hp : p.Prime) {N : Subgroup Y}
    (hc : ∀ x ∈ N, (∀ r ∈ CFSG.Open.pCoreOf p N, x * r = r * x) → x ∈ CFSG.Open.pCoreOf p N) :
    GLAPPrimeCoreOf p N = ⊥ := by
  have hPN : CFSG.Open.pCoreOf p N ≤ N := Subgroup.map_subtype_le _
  have hcomm : ∀ m ∈ GLAPPrimeCoreOf p N, ∀ x ∈ CFSG.Open.pCoreOf p N, m * x = x * m := by
    intro m hm x hx
    have hmN : m ∈ N := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le N hm
    have hxN : x ∈ N := hPN hx
    have hc1 : m * x * m⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p N := by
      have h1 : x * m⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p N :=
        CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem x hxN _
          ((GLAPPrimeCoreOf p N).inv_mem hm)
      have h2 := (GLAPPrimeCoreOf p N).mul_mem hm h1
      simpa only [mul_assoc] using h2
    have hc2 : m * x * m⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf p N :=
      (CFSG.Open.pCoreOf p N).mul_mem (conj_mem_pCoreOf hmN hx)
        ((CFSG.Open.pCoreOf p N).inv_mem hx)
    obtain ⟨k, hk⟩ := pow_eq_one_of_mem_pCoreOf hc2
    have hcop :=
      CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hc1
    have hone : orderOf (m * x * m⁻¹ * x⁻¹) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) (orderOf_dvd_of_pow_eq_one hk)
    have key : m * x * m⁻¹ * x⁻¹ = 1 := orderOf_eq_one_iff.1 hone
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 key)
  have hMP : GLAPPrimeCoreOf p N ≤ CFSG.Open.pCoreOf p N := fun m hm =>
    hc m (CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le N hm)
      (fun r hr => hcomm m hm r hr)
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨k, hk⟩ := pow_eq_one_of_mem_pCoreOf (hMP hm)
  have hcop :=
    CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hm
  have hone : orderOf m = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) (orderOf_dvd_of_pow_eq_one hk)
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 hone)

theorem glaPLayer_eq_bot_of_constrained {p : ℕ} (hp : p.Prime) {N H : Subgroup Y}
    (hHN : H ≤ N) (hn : (H.subgroupOf N).Normal)
    (hc : ∀ x ∈ N, (∀ r ∈ CFSG.Open.pCoreOf p N, x * r = r * x) → x ∈ CFSG.Open.pCoreOf p N) :
    GLAPLayer p H = ⊥ := by
  have hON : GLAPPrimeCoreOf p N = ⊥ := glaPPrimeCoreOf_eq_bot_of_constrained hp hc
  have hOH : GLAPPrimeCoreOf p H = ⊥ := by
    have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_normal_aux p hHN hn
    rw [hON] at h1
    exact le_bot_iff.1 h1
  have hPN : CFSG.Open.pCoreOf p N ≤ N := Subgroup.map_subtype_le _
  have hPnorm : ((CFSG.Open.pCoreOf p N).subgroupOf N).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa using conj_mem_pCoreOf g.2 hx⟩
  have hNP : N ≤ Subgroup.normalizer (CFSG.Open.pCoreOf p N : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).1 hPnorm
  refine eq_bot_iff.2 (sSup_le fun J hJ => ?_)
  have hJ' : GLAPComponent p H J := hJ
  exfalso
  have hJH : J ≤ H := hJ'.1
  have hsnJH : CFSG.Open.IsSubnormal J H := hJ'.2.1
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_glaPComponent_of_comm hp hJ'
      (fun g _ o ho => by
        rw [hOH, Subgroup.mem_bot] at ho
        rw [ho, one_mul, mul_one])
  have hsnHN : CFSG.Open.IsSubnormal H N :=
    CFSG.Open.IsSubnormal.step hHN hn (CFSG.Open.IsSubnormal.refl N)
  have hJN : J ≤ N := hJH.trans hHN
  have hcompN : CFSG.Assembly.IsComponentOf J N :=
    CFSG.Assembly.isComponentOf_iff_open.2
      ⟨hJN, CFSG.Open.IsSubnormal.trans hsnJH hsnHN, hJq⟩
  have hJP : J ≤ CFSG.Open.pCoreOf p N := by
    rcases comp_le_or_commute_aux hcompN hPN hNP with h | h
    · exact h
    · intro j hj
      have hjc : j ∈ Subgroup.centralizer (CFSG.Open.pCoreOf p N : Set Y) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h) hj
      exact hc j (hJN hj) (fun r hr => ((Subgroup.mem_centralizer_iff.1 hjc) r hr).symm)
  have hJp : IsPGroup p ↥J := by
    intro g
    obtain ⟨k, hk⟩ := pow_eq_one_of_mem_pCoreOf (hJP g.2)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent ↥J := hJp.isNilpotent
  haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
  haveI : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hJq
  exact Group.IsPerfect.not_isSolvable (↥J) inferInstance

end Constrained

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
