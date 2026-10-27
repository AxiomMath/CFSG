module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L57
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Config
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Residual

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups

namespace P58b3

@[expose] def OddAutInner (X : Type) [Group X] : Prop :=
  ∀ (α : MulAut X) (k : ℕ), Odd k → α ^ k ∈ (MulAut.conj : X →* MulAut X).range →
    α ∈ (MulAut.conj : X →* MulAut X).range

@[expose] def CyclicCenterTwo (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup X, P ≤ center X → IsPGroup 2 P → IsCyclic P

theorem oddAutInner_of_index {X : Type} [Group X] {m : ℕ}
    (h : (OuterAutomorphisms.inner X).index = 2 ^ m) : OddAutInner X :=
  fun _ _ hk hα => mem_of_pow_mem_of_index_eq_two_pow h hk hα

theorem cyclicCenterTwo_of_isCyclic {X : Type} [Group X] (h : IsCyclic (center X)) :
    CyclicCenterTwo X := fun _ hP _ =>
  isCyclic_of_injective (Subgroup.inclusion hP) (Subgroup.inclusion_injective hP)

theorem OddAutInner.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OddAutInner Y) : OddAutInner X := by
  intro α k hk hα
  obtain ⟨x, hx⟩ := hα
  have hβ : (MulAut.congr e α) ^ k ∈ (MulAut.conj : Y →* MulAut Y).range :=
    ⟨e x, by rw [← map_pow, ← hx, OuterAutomorphisms.congr_conj]⟩
  obtain ⟨y, hy⟩ := h _ k hk hβ
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hy]

theorem CyclicCenterTwo.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CyclicCenterTwo Y) : CyclicCenterTwo X := by
  intro P hP hP2
  have hPZ : P.map e.toMonoidHom ≤ center Y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    change e y * e x = e x * e y
    rw [← map_mul, ← map_mul, mem_center_iff.mp (hP hx) y]
  have hc := h _ hPZ (hP2.map e.toMonoidHom)
  exact isCyclic_of_surjective (P.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
    (P.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective

variable {G : Type} [Group G] [Finite G]

theorem le_sup_pPrimeCore_of_aut {M : Subgroup G} [hMn : M.Normal]
    (hM2 : ∀ g : G, ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ M)
    (ha : OddAutInner (↥M ⧸ pPrimeCore 2 ↥M)) (hb : CyclicCenterTwo (↥M ⧸ pPrimeCore 2 ↥M))
    {z : G} (hz : orderOf z = 2) (hzX : z ∈ M) :
    centralizer ({z} : Set G) ≤ (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map
      (centralizer {z}).subtype ⊔ M ⊓ centralizer {z} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({z} : Set G) with hHdef
  set D := M ⊓ H with hDdef
  set ψ : G →* MulAut (↥M ⧸ pPrimeCore 2 ↥M) :=
    UnbalancingLocal.conjQuotAction M (pPrimeCore 2 ↥M) with hψ
  set z' : ↥M := ⟨z, hzX⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact hz
  have hOMo : Odd (Nat.card (pPrimeCore 2 ↥M)) := F3L57.odd_card_pPrimeCore ↥M
  have hstep : ∀ h ∈ H, ∃ d ∈ D, d⁻¹ * h ∈ ψ.ker := by
    intro h hh
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
    have hhm : h ^ m ∈ M := hM2 _ a (by
      rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one])
    have hinner : ψ h ^ m ∈ (MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut _).range := by
      rw [← map_pow]
      exact ⟨_, (UnbalancingLocal.conjQuotAction_coe (Z := pPrimeCore 2 ↥M)
        (⟨h ^ m, hhm⟩ : ↥M)).symm⟩
    obtain ⟨x, hx⟩ := ha _ m hm hinner
    obtain ⟨m₀, rfl⟩ := QuotientGroup.mk_surjective x
    have hhz : h * z * h⁻¹ = z := by
      rw [mem_centralizer_singleton_iff] at hh
      rw [hh, mul_inv_cancel_right]
    have hfix : MulAut.conj (m₀ : ↥M ⧸ pPrimeCore 2 ↥M) (z' : ↥M ⧸ pPrimeCore 2 ↥M) =
        (z' : ↥M ⧸ pPrimeCore 2 ↥M) := by
      rw [hx, hψ, UnbalancingLocal.conjQuotAction_mk' h z' (by
        show h * z * h⁻¹ ∈ M
        rw [hhz]
        exact hzX)]
      exact congrArg _ (Subtype.ext hhz)
    have hcen : QuotientGroup.mk' (pPrimeCore 2 ↥M) m₀ ∈
        centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥M) z'} : Set (↥M ⧸ pPrimeCore 2 ↥M)) := by
      rw [mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hfix
      exact hfix
    rw [← FooteLit.map_centralizer_mk'_of_odd hOMo hz'2] at hcen
    obtain ⟨d', hd', hd'm⟩ := hcen
    have hdH : (d' : G) ∈ H := by
      rw [hHdef, mem_centralizer_singleton_iff]
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hd'
      exact congrArg Subtype.val hd'
    refine ⟨d', ⟨d'.2, hdH⟩, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hx, hψ,
      UnbalancingLocal.conjQuotAction_coe (Z := pPrimeCore 2 ↥M) d']
    have hdm : (d' : ↥M ⧸ pPrimeCore 2 ↥M) = (m₀ : ↥M ⧸ pPrimeCore 2 ↥M) := hd'm
    rw [hdm, inv_mul_cancel]
  set W := ψ.ker ⊓ H with hWdef
  have hWH : W ≤ H := inf_le_right
  have hWn : (W.subgroupOf H).Normal := by
    rw [hWdef, inf_subgroupOf_right]
    infer_instance
  have hcyc : ∀ S : Sylow 2 ↥W, IsCyclic S := by
    intro S
    set T : Subgroup G := (S : Subgroup ↥W).map W.subtype with hTdef
    have h2T : ∀ t ∈ T, ∃ k : ℕ, t ^ 2 ^ k = 1 := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨k, hk⟩ := S.2 ⟨s, hs⟩
      exact ⟨k, by simpa using congrArg (fun y : ↥(S : Subgroup ↥W) => ((y : ↥W) : G)) hk⟩
    have hTM : T ≤ M := fun t ht => by
      obtain ⟨k, hk⟩ := h2T t ht
      exact hM2 t k hk
    have hTk : T ≤ ψ.ker := by
      rintro _ ⟨s, -, rfl⟩
      exact (mem_inf.mp s.2).1
    let φ : ↥T →* ↥M ⧸ pPrimeCore 2 ↥M :=
      (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hTM)
    have hφinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro t ht
      rw [MonoidHom.mem_ker] at ht
      have h1 : Subgroup.inclusion hTM t ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp ht
      obtain ⟨k, hk⟩ := h2T t t.2
      have h2 : (Subgroup.inclusion hTM t) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      have h3' := F3L57.eq_one_of_pow_two_pow_of_mem hOMo h1 h2
      rw [mem_bot]
      exact Subgroup.inclusion_injective hTM (h3'.trans (map_one _).symm)
    have hφZ : φ.range ≤ center (↥M ⧸ pPrimeCore 2 ↥M) := by
      rintro _ ⟨t, rfl⟩
      have h1 : ψ (t : G) = 1 := hTk t.2
      have h2 := UnbalancingLocal.conjQuotAction_coe (Z := pPrimeCore 2 ↥M)
        (Subgroup.inclusion hTM t)
      rw [← hψ] at h2
      have h3' : ψ (t : G) = MulAut.conj (φ t) := h2
      rw [h1] at h3'
      rw [mem_center_iff]
      intro g
      have := congrArg (fun α : MulAut (↥M ⧸ pPrimeCore 2 ↥M) => α g) h3'
      simp only [MulAut.one_apply, MulAut.conj_apply] at this
      rw [eq_mul_inv_iff_mul_eq] at this
      exact this
    have hφ2 : IsPGroup 2 φ.range := by
      rintro ⟨_, ⟨t, rfl⟩⟩
      obtain ⟨k, hk⟩ := h2T t t.2
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : t ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hk', map_one]
    have hTc : IsCyclic ↥T := by
      have := hb _ hφZ hφ2
      exact isCyclic_of_surjective (MonoidHom.ofInjective hφinj).symm.toMonoidHom
        (MonoidHom.ofInjective hφinj).symm.surjective
    exact isCyclic_of_surjective
      ((S : Subgroup ↥W).equivMapOfInjective W.subtype W.subtype_injective).symm.toMonoidHom
      ((S : Subgroup ↥W).equivMapOfInjective W.subtype W.subtype_injective).symm.surjective
  have hW2 : ∀ x ∈ W, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ D := fun x hx k hk =>
    ⟨hM2 x k hk, hWH hx⟩
  have hWle := F3L57.le_sup_of_isCyclic_sylow hWH hWn hcyc hW2
  intro h hh
  obtain ⟨d, hdD, hdk⟩ := hstep h hh
  have hw : d⁻¹ * h ∈ W := mem_inf.mpr ⟨hdk, mul_mem (inv_mem (mem_inf.mp hdD).2) hh⟩
  have h1 : h = d * (d⁻¹ * h) := by group
  rw [h1]
  exact mul_mem (mem_sup_right hdD) (hWle hw)

theorem harris82Lemma57_of_aut {M : Subgroup G} [M.Normal]
    (hM2 : ∀ g : G, ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ M)
    (ha : OddAutInner (↥M ⧸ pPrimeCore 2 ↥M)) (hb : CyclicCenterTwo (↥M ⧸ pPrimeCore 2 ↥M))
    {z : G} (hz : orderOf z = 2) (hzX : z ∈ M) {J : Subgroup G}
    (hJ : IsSolvableTwoComponentIn J (centralizer {z})) :
    IsSolvableTwoComponentIn (J ⊓ M) (M ⊓ centralizer {z}) ∧
      J = (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ (J ⊓ M) ∧
      GH74.GLS.oPrimeResidualOf 2 J = GH74.GLS.oPrimeResidualOf 2 (J ⊓ M) := by
  classical
  set H := centralizer ({z} : Set G) with hHdef
  set OH := (pPrimeCore 2 ↥H).map H.subtype with hOHdef
  obtain ⟨hJH, hJs, hJO, hJiso⟩ := hJ
  have hOHJ : OH ≤ J := by
    rw [hOHdef, ← hJO]
    exact map_subtype_le _
  have hHD := le_sup_pPrimeCore_of_aut hM2 ha hb hz hzX
  set J₁ := J ⊓ M with hJ₁def
  have hJ₁D : J₁ ≤ M ⊓ H := le_inf inf_le_right (inf_le_left.trans hJH)
  have hDn : M ⊓ H ≤ normalizer (OH : Set G) :=
    inf_le_right.trans (F3L57.le_normalizer_map_subtype (pPrimeCore 2 ↥H))
  have hJeq : J = OH ⊔ J₁ := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ ((M ⊓ H ⊔ OH : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact hHD (hJH hx)
      rw [coe_mul_of_left_le_normalizer_right _ _ hDn] at hx'
      obtain ⟨d, hd, o, ho, rfl⟩ := hx'
      have hdJ : d ∈ J := by
        have h1 : d = d * o * o⁻¹ := by group
        rw [h1]
        exact mul_mem hx (inv_mem (hOHJ ho))
      rw [sup_comm]
      exact mul_mem_sup ⟨hdJ, hd.1⟩ ho
    · exact sup_le hOHJ inf_le_left
  have hJ₁J : (J₁.subgroupOf J).Normal := by
    rw [hJ₁def, inf_comm, inf_subgroupOf_right]
    infer_instance
  have hJ₁sH : (J₁.subgroupOf H).IsSubnormal := by
    have hJ₁J' : ((J₁.subgroupOf H).subgroupOf (J.subgroupOf H)).Normal := by
      have heq : (J₁.subgroupOf H).subgroupOf (J.subgroupOf H) =
          (J₁.subgroupOf J).comap (subgroupOfEquivOfLe hJH).toMonoidHom := by
        ext x
        exact Iff.rfl
      rw [heq]
      exact hJ₁J.comap _
    exact IsSubnormal.step _ _ (subgroupOf_mono H inf_le_left) hJs hJ₁J'
  have hJ₁s : (J₁.subgroupOf (M ⊓ H)).IsSubnormal :=
    F3L57.isSubnormal_subgroupOf_of_le inf_le_right hJ₁sH
  have hDH : ((M ⊓ H).subgroupOf H).Normal := by
    rw [inf_subgroupOf_right]
    infer_instance
  have hOD : (pPrimeCore 2 ↥(M ⊓ H)).map (M ⊓ H).subtype ≤ OH :=
    F3L57.map_pPrimeCore_le_of_normal inf_le_right hDH
  have hOJ₁ : (pPrimeCore 2 ↥J₁).map J₁.subtype = (pPrimeCore 2 ↥(M ⊓ H)).map (M ⊓ H).subtype := by
    rw [F3L57.map_pPrimeCore_eq_inf hJ₁D hJ₁s]
    refine inf_eq_right.mpr (le_inf (hOD.trans hOHJ) ?_)
    exact (map_subtype_le _).trans inf_le_left
  obtain ⟨-, -, -, ⟨esat⟩⟩ := F3.saturate (hJ₁D.trans inf_le_right) hJ₁sH
  have hsup : J₁ ⊔ OH = J := by rw [sup_comm, ← hJeq]
  let eJ : ↥J ⧸ pPrimeCore 2 ↥J ≃* ↥J₁ ⧸ pPrimeCore 2 ↥J₁ :=
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hsup).symm
      (pPrimeCore_map_iso 2 _)).trans esat
  have hJ₁iso : Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* PSL(2, ZMod 3)) ∨
      Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, ZMod 3)) := by
    rcases hJiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨eJ.symm.trans e⟩
    · exact Or.inr ⟨eJ.symm.trans e⟩
  have hO2 : GH74.GLS.oPrimeResidualOf 2 J = GH74.GLS.oPrimeResidualOf 2 J₁ := by
    simp only [GH74.GLS.oPrimeResidualOf, GH74.GLS.oPrimeResidual, MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, coe_subtype]
    constructor
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      have hyM : (y : G) ∈ M := hM2 _ k (by simpa using congrArg Subtype.val hk)
      exact ⟨⟨y, y.2, hyM⟩, ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩, rfl⟩
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      exact ⟨⟨y, y.2.1⟩, ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩, rfl⟩
  exact ⟨⟨hJ₁D, hJ₁s, hOJ₁, hJ₁iso⟩, hJeq, hO2⟩

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime {K : Subgroup G} {l : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : l ^ a ∈ K) (hb : l ^ b ∈ K) : l ∈ K := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hl : l = (l ^ (a : ℤ)) ^ Nat.gcdA a b * (l ^ (b : ℤ)) ^ Nat.gcdB a b := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [hl]
  exact mul_mem (zpow_mem (by rwa [zpow_natCast]) _) (zpow_mem (by rwa [zpow_natCast]) _)

theorem mem_of_mem_sup_of_pow {K L : Subgroup G} (hLN : L ≤ normalizer (K : Set G))
    (hO : GH74.GLS.oPrimeResidualOf 2 L ≤ K) {g : G} (hg : g ∈ K ⊔ L) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g ∈ K := by
  rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hLN] at hg
  obtain ⟨l, hl, k₀, hk₀, rfl⟩ := hg
  have hpow : ∀ n : ℕ, (l ^ n)⁻¹ * (l * k₀) ^ n ∈ K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : (l ^ (n + 1))⁻¹ * (l * k₀) ^ (n + 1) =
          l⁻¹ * ((l ^ n)⁻¹ * (l * k₀) ^ n) * l⁻¹⁻¹ * k₀ := by
        rw [pow_succ, pow_succ, mul_inv_rev, inv_inv]
        simp only [mul_assoc]
      rw [h1]
      exact mul_mem ((mem_normalizer_iff.mp (inv_mem (hLN hl)) _).mp ih) hk₀
  have hl2k : l ^ 2 ^ k ∈ K := by
    have h1 := hpow (2 ^ k)
    rw [hk, mul_one, inv_mem_iff] at h1
    exact h1
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  have hlm : l ^ m ∈ K := hO (by
    rw [Sol78.oPrimeResidualOf_eq_closure]
    refine subset_closure ⟨pow_mem hl m, a, ?_⟩
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one])
  exact mul_mem (mem_of_pow_mem_of_coprime
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)).symm hl2k hlm) hk₀

omit [Finite G] in
theorem isSubnormal_sup_of_normal {N L C : Subgroup G} (hNC : N ≤ C) (hLC : L ≤ C)
    (hN : (N.subgroupOf C).Normal) (hL : (L.subgroupOf C).IsSubnormal) :
    ((N ⊔ L).subgroupOf C).IsSubnormal := by
  rw [subgroupOf_sup hNC hLC, ← QuotientGroup.comap_map_mk']
  exact (hL.map (QuotientGroup.mk'_surjective _)).comap _

theorem lemma57_fourGroup {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2) {L K : Subgroup G}
    (hL : IsSolvableTwoComponentIn L (centralizer {z₁} ⊓ centralizer {z₂}))
    (hK₁ : K ≤ centralizer {z₁}) (hO : GH74.GLS.oPrimeResidualOf 2 L ≤ K)
    (hN : centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G)) (hz₂K : z₂ ∈ K)
    (ha : OddAutInner (↥K ⧸ pPrimeCore 2 ↥K)) (hb : CyclicCenterTwo (↥K ⧸ pPrimeCore 2 ↥K)) :
    IsSolvableTwoComponentIn (L ⊓ K) (K ⊓ centralizer {z₂}) ∧
      L = (pPrimeCore 2 ↥(centralizer {z₁} ⊓ centralizer {z₂} : Subgroup G)).map
        (centralizer {z₁} ⊓ centralizer {z₂} : Subgroup G).subtype ⊔ (L ⊓ K) ∧
      GH74.GLS.oPrimeResidualOf 2 L = GH74.GLS.oPrimeResidualOf 2 (L ⊓ K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CW : Subgroup G := centralizer {z₁} ⊓ centralizer {z₂} with hCW
  set OW := (pPrimeCore 2 ↥CW).map CW.subtype with hOW
  obtain ⟨hLCW, hLs, hLO, hLiso⟩ := hL
  have hLN : L ≤ normalizer (K : Set G) := hLCW.trans hN
  have hOWL : OW ≤ L := by
    rw [hOW, ← hLO]
    exact map_subtype_le _
  set N : Subgroup G := K ⊓ centralizer {z₂} with hNdef
  have hNCW : N ≤ CW := le_inf (inf_le_left.trans hK₁) inf_le_right
  have hNn : (N.subgroupOf CW).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hNCW]
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    have hgK := mem_normalizer_iff.mp (hN hg) x
    have hgC : g ∈ centralizer ({z₂} : Set G) := (mem_inf.mp hg).2
    constructor
    · intro hx
      obtain ⟨hxK, hxz⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨hgK.mp hxK, mul_mem (mul_mem hgC hxz) (inv_mem hgC)⟩
    · intro hx
      obtain ⟨hxK, hxz⟩ := mem_inf.mp hx
      have h1 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      refine mem_inf.mpr ⟨hgK.mpr hxK, ?_⟩
      rw [h1]
      exact mul_mem (mul_mem (inv_mem hgC) hxz) hgC
  set E := K ⊔ L with hE
  have hKE : K ≤ E := le_sup_left
  have hLE : L ≤ E := le_sup_right
  have hEN : E ≤ normalizer (K : Set G) := sup_le le_normalizer hLN
  have hMn : (K.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hKE).mpr hEN
  have hM2 : ∀ g : ↥E, ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ K.subgroupOf E := fun g k hk =>
    mem_subgroupOf.mpr (mem_of_mem_sup_of_pow hLN hO g.2 (by
      simpa using congrArg Subtype.val hk))
  let eK : ↥(K.subgroupOf E) ≃* ↥K := subgroupOfEquivOfLe hKE
  let eX : ↥(K.subgroupOf E) ⧸ pPrimeCore 2 ↥(K.subgroupOf E) ≃* ↥K ⧸ pPrimeCore 2 ↥K :=
    QuotientGroup.congr _ _ eK (pPrimeCore_map_iso 2 eK)
  set z' : ↥E := ⟨z₂, hKE hz₂K⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact hz₂
  have hle := le_sup_pPrimeCore_of_aut hM2 (ha.of_mulEquiv eX) (hb.of_mulEquiv eX) hz'2
    (mem_subgroupOf.mpr hz₂K)
  set A : Subgroup G := centralizer {z₂} ⊓ E with hAdef
  have hAE : A ≤ E := inf_le_right
  have hCz : centralizer ({z'} : Set ↥E) = A.subgroupOf E := by
    rw [hAdef, inf_subgroupOf_right]
    ext x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      Subtype.ext_iff]
    rfl
  rw [hCz] at hle
  have hmap := map_mono (f := E.subtype) hle
  rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hAE,
    F3S7.map_pPrimeCore_subgroupOf hAE] at hmap
  set OA := (pPrimeCore 2 ↥A).map A.subtype with hOA
  have hKA : ((K.subgroupOf E) ⊓ A.subgroupOf E).map E.subtype ≤ K ⊓ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_subgroupOf.mp hx.1, mem_subgroupOf.mp hx.2⟩
  have hA : A ≤ OA ⊔ (K ⊓ A) := hmap.trans (sup_le_sup_left hKA _)
  have hAeq : A = N ⊔ L := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxz, hxE⟩ := mem_inf.mp hx
      rw [hE, sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hLN] at hxE
      obtain ⟨l, hl, k₀, hk₀, rfl⟩ := hxE
      have hlz : l ∈ centralizer ({z₂} : Set G) := (mem_inf.mp (hLCW hl)).2
      have hk₀z : k₀ ∈ centralizer ({z₂} : Set G) := by
        have h1 : k₀ = l⁻¹ * (l * k₀) := by group
        rw [h1]
        exact mul_mem (inv_mem hlz) hxz
      rw [sup_comm]
      exact mul_mem_sup hl ⟨hk₀, hk₀z⟩
    · exact sup_le (le_inf inf_le_right (inf_le_left.trans hKE))
        (le_inf (hLCW.trans inf_le_right) hLE)
  have hACW : A ≤ CW := by rw [hAeq]; exact sup_le hNCW hLCW
  have hAs : (A.subgroupOf CW).IsSubnormal := by
    rw [hAeq]
    exact isSubnormal_sup_of_normal hNCW hLCW hNn hLs
  have hOAW : OA ≤ OW := by
    rw [hOA, F3L57.map_pPrimeCore_eq_inf hACW hAs]
    exact inf_le_right
  have hLeq : L = OW ⊔ (L ⊓ K) := by
    apply le_antisymm
    · intro l hl
      have hlA : l ∈ A := by rw [hAeq]; exact mem_sup_right hl
      have hKAn : K ⊓ A ≤ normalizer (OA : Set G) :=
        inf_le_right.trans (F3L57.le_normalizer_map_subtype (pPrimeCore 2 ↥A))
      have hl' : l ∈ ((K ⊓ A ⊔ OA : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact hA hlA
      rw [coe_mul_of_left_le_normalizer_right _ _ hKAn] at hl'
      obtain ⟨d, hd, o, ho, rfl⟩ := hl'
      have hoL : o ∈ L := hOWL (hOAW ho)
      have hdL : d ∈ L := by
        have h1 : d = d * o * o⁻¹ := by group
        rw [h1]
        exact mul_mem hl (inv_mem hoL)
      rw [sup_comm]
      exact mul_mem_sup ⟨hdL, hd.1⟩ (hOAW ho)
    · exact sup_le hOWL inf_le_left
  set J₁ := L ⊓ K with hJ₁def
  have hJ₁N : J₁ ≤ N := le_inf inf_le_right (inf_le_left.trans (hLCW.trans inf_le_right))
  have hJ₁CW : J₁ ≤ CW := hJ₁N.trans hNCW
  have hJ₁L : (J₁.subgroupOf L).Normal := by
    rw [hJ₁def, inf_comm, normal_subgroupOf_iff_le_normalizer_inf]
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    have hgK := mem_normalizer_iff.mp (hLN hg) x
    constructor
    · intro hx
      obtain ⟨hxK, hxL⟩ := mem_inf.mp (mem_inf.mp hx).1
      have hgx : g * x * g⁻¹ ∈ L := mul_mem (mul_mem hg hxL) (inv_mem hg)
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hgK.mp hxK, hgx⟩, hgx⟩
    · intro hx
      obtain ⟨hxK, hxL⟩ := mem_inf.mp (mem_inf.mp hx).1
      have hxL' : x ∈ L := by
        have h1 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [h1]
        exact mul_mem (mul_mem (inv_mem hg) hxL) hg
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hgK.mpr hxK, hxL'⟩, hxL'⟩
  have hJ₁sCW : (J₁.subgroupOf CW).IsSubnormal := by
    have hJ₁L' : ((J₁.subgroupOf CW).subgroupOf (L.subgroupOf CW)).Normal := by
      have heq : (J₁.subgroupOf CW).subgroupOf (L.subgroupOf CW) =
          (J₁.subgroupOf L).comap (subgroupOfEquivOfLe hLCW).toMonoidHom := by
        ext x
        exact Iff.rfl
      rw [heq]
      exact hJ₁L.comap _
    exact IsSubnormal.step _ _ (subgroupOf_mono CW inf_le_left) hLs hJ₁L'
  have hJ₁sN : (J₁.subgroupOf N).IsSubnormal := F3L57.isSubnormal_subgroupOf_of_le hNCW hJ₁sCW
  have hON : (pPrimeCore 2 ↥N).map N.subtype ≤ OW :=
    F3L57.map_pPrimeCore_le_of_normal hNCW hNn
  have hOJ₁ : (pPrimeCore 2 ↥J₁).map J₁.subtype = (pPrimeCore 2 ↥N).map N.subtype := by
    rw [F3L57.map_pPrimeCore_eq_inf hJ₁N hJ₁sN]
    refine inf_eq_right.mpr (le_inf (hON.trans hOWL) ?_)
    exact (map_subtype_le _).trans inf_le_left
  obtain ⟨-, -, -, ⟨esat⟩⟩ := F3.saturate hJ₁CW hJ₁sCW
  have hsup : J₁ ⊔ OW = L := by rw [sup_comm, ← hLeq]
  let eJ : ↥L ⧸ pPrimeCore 2 ↥L ≃* ↥J₁ ⧸ pPrimeCore 2 ↥J₁ :=
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hsup).symm
      (pPrimeCore_map_iso 2 _)).trans esat
  have hJ₁iso : Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* PSL(2, ZMod 3)) ∨
      Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, ZMod 3)) := by
    rcases hLiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨eJ.symm.trans e⟩
    · exact Or.inr ⟨eJ.symm.trans e⟩
  have hO2 : GH74.GLS.oPrimeResidualOf 2 L = GH74.GLS.oPrimeResidualOf 2 J₁ := by
    simp only [GH74.GLS.oPrimeResidualOf, GH74.GLS.oPrimeResidual, MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, coe_subtype]
    constructor
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      have hyK : (y : G) ∈ K := hO (by
        rw [Sol78.oPrimeResidualOf_eq_closure]
        exact subset_closure ⟨y.2, k, by simpa using congrArg Subtype.val hk⟩)
      exact ⟨⟨y, y.2, hyK⟩, ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩, rfl⟩
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      exact ⟨⟨y, y.2.1⟩, ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩, rfl⟩
  exact ⟨⟨hJ₁N, hJ₁sN, hOJ₁, hJ₁iso⟩, hLeq, hO2⟩

theorem lemma57_fourGroup_map {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2) {L K : Subgroup G}
    (hL : IsSolvableTwoComponentIn L (centralizer {z₁} ⊓ centralizer {z₂}))
    (hK₁ : K ≤ centralizer {z₁}) (hO : GH74.GLS.oPrimeResidualOf 2 L ≤ K)
    (hN : centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G)) (hz₂K : z₂ ∈ K)
    (ha : OddAutInner (↥K ⧸ pPrimeCore 2 ↥K)) (hb : CyclicCenterTwo (↥K ⧸ pPrimeCore 2 ↥K)) :
    IsSolvableTwoComponentIn (((L ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)))
      (centralizer {(QuotientGroup.mk (⟨z₂, hz₂K⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K)}) := by
  obtain ⟨h1, -, -⟩ := lemma57_fourGroup hz₂ hL hK₁ hO hN hz₂K ha hb
  have h2 := F3S7.isSolvableTwoComponentIn_subgroupOf h1.1 inf_le_left h1
  have hC : (K ⊓ centralizer {z₂}).subgroupOf K = centralizer {(⟨z₂, hz₂K⟩ : ↥K)} := by
    rw [inf_comm, inf_subgroupOf_right]
    ext x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      Subtype.ext_iff]
    rfl
  rw [hC] at h2
  exact F3L221.isSolvableTwoComponentIn_map_mk (by rw [Subgroup.orderOf_mk]; exact hz₂) h2

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
