module

public import CFSG.CGT.PushingUpLit.SolK.Inputs
public import CFSG.CGT.PushingUpLit.SolK.Kernel
public import CFSG.CGT.PushingUpLit.STT.NatAlt
public import CFSG.CGT.PushingUpLit.STT.SzU3
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
public import CFSG.CGT.PushingUpLit.SolK.Fusion

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.Timmesfeld75
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

@[expose] def TightSmallGroupOrders : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (StatedClassicalModel G .PSL 3 3 1 ∨ StatedClassicalModel G .PSU 3 3 1 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 ∨
      CFSG.Blueprint.LieModel G .G2 0 3 1 ∨ StatedClassicalModel G .PSL 3 2 2) →
    ∀ P : Subgroup G, IsPGroup 2 P → Nat.card P ≤ 64

structure TightDataPlus {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}
    (S : SolCfg G M X n) : Prop extends TightData S where
  ti : ∀ g : G, g ∉ M → rOf M X ⊓ conjSubgroup g (rOf M X) = ⊥
  nonweak : rOf M X ≠ ⊥ →
    ∃ g : G, conjSubgroup g (rOf M X) ≤ M ∧ conjSubgroup g (rOf M X) ≠ rOf M X

section Conj

variable {G : Type} [Group G]

theorem isPLocal_two_conj {H : Subgroup G} (hH : IsPLocal 2 H) (g : G) :
    IsPLocal 2 (H.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP, hP2, hHP⟩ := hH
  refine ⟨P.map (MulAut.conj g).toMonoidHom,
    fun h => hP ((Subgroup.map_eq_bot_iff_of_injective P (MulAut.conj g).injective).mp h),
    hP2.map _, ?_⟩
  rw [hHP, Subgroup.map_equiv_normalizer_eq]

theorem isMaximalTwoLocal_conj {M : Subgroup G} (hM : IsMaximalTwoLocal M) (g : G) :
    IsMaximalTwoLocal (M.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨isPLocal_two_conj hM.1 g, fun H hlt hH => ?_⟩
  have hH' := isPLocal_two_conj hH g⁻¹
  have hback : (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
    rw [Subgroup.map_map]
    have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply]
      group
    rw [this, Subgroup.map_id]
  have hlt' : M < H.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hback] at hlt
    exact (MulEquiv.mapSubgroup (MulAut.conj g)).lt_iff_lt.mp hlt
  exact hM.2 _ hlt' hH'

end Conj

section Basic

variable {G : Type} [Group G]

theorem eq_one_of_odd_card {H : Subgroup G} (hH : Odd (Nat.card ↥H)) {c : G} (hc : c ∈ H) {j : ℕ}
    (hj : c ^ (2 ^ j) = 1) : c = 1 := by
  have h1 : orderOf c ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨c, hc⟩ : ↥H)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf c ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
  have hcop : Nat.Coprime (Nat.card H) (2 ^ j) := (Nat.coprime_two_right.2 hH).pow_right j
  have h3 : orderOf c ∣ Nat.gcd (Nat.card H) (2 ^ j) := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hcop] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem comm_of_cyclic_or_elem {R : Subgroup G}
    (hab : (IsCyclic ↥R ∧ Nat.card ↥R = 4) ∨ IsElemAbelian 2 R) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  intro a ha b hb
  rcases hab with ⟨hcyc, -⟩ | ⟨hcomm, -⟩
  · let _ := IsCyclic.commGroup (α := ↥R)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥R) ⟨b, hb⟩)
  · exact congrArg Subtype.val (hcomm.is_comm.comm (⟨a, ha⟩ : ↥R) ⟨b, hb⟩)

theorem two_element_mem_of_sylow {C : Subgroup G} (R : Sylow 2 ↥C)
    (hRO : (R : Subgroup ↥C).map C.subtype = pCoreOf 2 C) {c : G} (hc : c ∈ C) {j : ℕ}
    (hj : c ^ (2 ^ j) = 1) : c ∈ pCoreOf 2 C := by
  have hRG2 : IsPGroup 2 (pCoreOf 2 C) := isPGroup_pCoreOf' C
  have hZ2 : IsPGroup 2 (Subgroup.zpowers c) := by
    have hord : orderOf c ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hZC : Subgroup.zpowers c ≤ C := (Subgroup.zpowers_le).2 hc
  have hZN : Subgroup.zpowers c ≤ Subgroup.normalizer (pCoreOf 2 C : Set G) := by
    intro x hx
    have hxC : x ∈ C := hZC hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => pCoreOf_normalized C hxC hy, fun hy => ?_⟩
    have := pCoreOf_normalized C (C.inv_mem hxC) hy
    simpa [mul_assoc] using this
  have hP2 : IsPGroup 2 (pCoreOf 2 C ⊔ Subgroup.zpowers c : Subgroup G) :=
    hRG2.to_sup_of_normal_left' hZ2 hZN
  have hPC : pCoreOf 2 C ⊔ Subgroup.zpowers c ≤ C := sup_le (pCoreOf_le_self C) hZC
  have hQ2 : IsPGroup 2 ↥((pCoreOf 2 C ⊔ Subgroup.zpowers c).subgroupOf C) :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  have hRQ : (R : Subgroup ↥C) ≤ (pCoreOf 2 C ⊔ Subgroup.zpowers c).subgroupOf C := fun x hx => by
    rw [Subgroup.mem_subgroupOf]
    refine (le_sup_left : pCoreOf 2 C ≤ pCoreOf 2 C ⊔ Subgroup.zpowers c) ?_
    rw [← hRO]
    exact ⟨x, hx, rfl⟩
  have hmax := R.is_maximal' hQ2 hRQ
  have hcQ : (⟨c, hc⟩ : ↥C) ∈ (pCoreOf 2 C ⊔ Subgroup.zpowers c).subgroupOf C := by
    rw [Subgroup.mem_subgroupOf]
    exact (le_sup_right : Subgroup.zpowers c ≤ pCoreOf 2 C ⊔ Subgroup.zpowers c)
      (Subgroup.mem_zpowers c)
  rw [hmax] at hcQ
  have : c ∈ (R : Subgroup ↥C).map C.subtype := ⟨⟨c, hc⟩, hcQ, rfl⟩
  rwa [hRO] at this

end Basic

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem mem_of_conj_le (g : G) (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ M) : g ∈ M := by
  set M' : Subgroup G := M.map (MulAut.conj g⁻¹).toMonoidHom with hM'
  have hmax : IsMaximalTwoLocal M' := isMaximalTwoLocal_conj S.hyp.maxLocal g⁻¹
  have hXM' : (X : Set G) ⊆ M' := fun x hx => ⟨g * x * g⁻¹, hg x hx, by
    simp
    group⟩
  have hmem : M' ∈ maximalTwoLocalsContaining (X : Set G) := ⟨hmax, hXM'⟩
  rw [S.hyp.unique] at hmem
  have hM'M : M' = M := hmem
  have hconj : ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro m hm
    rw [← hM'M] at hm
    obtain ⟨m', hm', hm'e⟩ := hm
    have : g * m * g⁻¹ = m' := by
      rw [← hm'e]
      simp
      group
    rw [this]
    exact hm'
  have hconj' : ∀ m ∈ M, g⁻¹ * m * g ∈ M := by
    intro m hm
    have : g⁻¹ * m * g ∈ M' := ⟨m, hm, by simp⟩
    rwa [hM'M] at this
  have hgN : g ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff.2 fun m => ⟨fun hm => hconj m hm, fun hm => by
      have := hconj' _ hm
      simpa [mul_assoc] using this⟩
  have hgN' : g⁻¹ ∈ Subgroup.normalizer (M : Set G) := (Subgroup.normalizer _).inv_mem hgN
  have hnormM : ∀ n ∈ Subgroup.normalizer (M : Set G), ∀ k ∈ M, n * k * n⁻¹ ∈ M :=
    fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk
  rw [← S.normalizer_Q_eq]
  refine Subgroup.mem_normalizer_iff.2 fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · exact pCoreOf_normalized_of_normal hnormM hgN hq
  · have := pCoreOf_normalized_of_normal hnormM hgN' hq
    simpa [mul_assoc] using this

theorem centralizer_X_le_M : Subgroup.centralizer (X : Set G) ≤ M := by
  have hW : S.D.W ≠ ⊥ := S.W_ne_bot
  have hY : pCoreOf 2 X ≠ ⊥ := fun h => hW (le_bot_iff.1 (h ▸ ModData.W_le_Y S.D))
  have hloc : IsPLocal 2 (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
    ⟨pCoreOf 2 X, hY, isPGroup_pCoreOf' X, rfl⟩
  have hXH : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => pCoreOf_normalized X hx hy, fun hy => ?_⟩
    have := pCoreOf_normalized X (X.inv_mem hx) hy
    simpa [mul_assoc] using this
  have hle := local_le_of_unique S.hyp.unique hloc hXH
  intro c hc
  have hcN : c ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) hc
  have hnormX : ∀ n ∈ Subgroup.normalizer (X : Set G), ∀ k ∈ X, n * k * n⁻¹ ∈ X :=
    fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk
  refine hle ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => pCoreOf_normalized_of_normal hnormX hcN hy, fun hy => ?_⟩
  have hcN' : c⁻¹ ∈ Subgroup.normalizer (X : Set G) := (Subgroup.normalizer _).inv_mem hcN
  have := pCoreOf_normalized_of_normal hnormX hcN' hy
  simpa [mul_assoc] using this

theorem mem_of_common_involution {g z : G} (hzC : z ∈ Subgroup.centralizer (X : Set G))
    (hz2 : orderOf z = 2) (hgz : g * z * g⁻¹ ∈ Subgroup.centralizer (X : Set G)) : g ∈ M := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; simp)
  have hZ : Subgroup.zpowers z ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hz1
  have hloc : IsPLocal 2 (Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) :=
    ⟨_, hZ, hZ2, rfl⟩
  have hCN : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hxz : ∀ x ∈ X, x * z * x⁻¹ = z := fun x hx => by
    have := Subgroup.mem_centralizer_iff.1 hzC x hx
    rw [this]
    group
  have hXN : X ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := fun x hx =>
    hCN (mem_centralizer_zpowers_iff.2 (hxz x hx))
  have hle := local_le_of_unique S.hyp.unique hloc hXN
  have hconj : ∀ x ∈ X, g⁻¹ * x * g⁻¹⁻¹ ∈ M := by
    intro x hx
    rw [inv_inv]
    have hc := Subgroup.mem_centralizer_iff.1 hgz x hx
    refine hle (hCN (mem_centralizer_zpowers_iff.2 ?_))
    calc g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by group
      _ = z := by rw [hc]; group
  have h1 : g⁻¹ ∈ M := S.mem_of_conj_le g⁻¹ hconj
  simpa using M.inv_mem h1

theorem M_le_normalizer_C :
    M ≤ Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ M, ∀ c ∈ Subgroup.centralizer (X : Set G),
      m * c * m⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro m hm c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : m⁻¹ * x * m ∈ X := by
      have := S.xnorm.normal m⁻¹ (M.inv_mem hm) x hx
      simpa using this
    have h1 := hc _ hx'
    calc x * (m * c * m⁻¹) = m * ((m⁻¹ * x * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * x := by group
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨key m hm c, fun h => by
    have := key m⁻¹ (M.inv_mem hm) _ h
    simpa [mul_assoc] using this⟩

theorem normalizer_C_eq (hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))) :
    Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) = M := by
  refine le_antisymm (fun g hg => ?_) S.M_le_normalizer_C
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (X : Set G))) 2
    (even_iff_two_dvd.1 hev)
  have hz2 : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  exact S.mem_of_common_involution z.2 hz2 ((Subgroup.mem_normalizer_iff.1 hg (z : G)).1 z.2)

theorem tightlyEmbedded_C (hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))) :
    TightlyEmbedded (Subgroup.centralizer (X : Set G)) :=
  StandardSubgroupAPI.tightlyEmbedded_of_involution hev fun g _ hz hz2 =>
    S.M_le_normalizer_C (S.mem_of_common_involution (Subgroup.mem_inf.1 hz).1 hz2
      ((mem_rightConjugate_iff _ g _).1 (Subgroup.mem_inf.1 hz).2))

theorem rOf_eq_pCoreOf_C :
    rOf M X = pCoreOf 2 (Subgroup.centralizer (X : Set G)) := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  have hCM : C ≤ M := S.centralizer_X_le_M
  have hCnorm : ∀ m ∈ M, ∀ c ∈ C, m * c * m⁻¹ ∈ C := fun m hm c hc =>
    (Subgroup.mem_normalizer_iff.1 (S.M_le_normalizer_C hm) c).1 hc
  refine le_antisymm ?_ ?_
  · refine le_pCoreOf_of_normalized (fun r hr => hr.2) (fun c hc r hr => ?_)
      (isPGroup_of_le (isPGroup_pCoreOf' M) inf_le_left)
    exact Subgroup.mem_inf.2 ⟨pCoreOf_normalized M (hCM hc) hr.1, hCnorm c (hCM hc) r hr.2⟩
  · intro x hx
    have hQ : pCoreOf 2 C ≤ pCoreOf 2 M :=
      le_pCoreOf_of_normalized ((pCoreOf_le_self C).trans hCM)
        (fun m hm y hy => pCoreOf_normalized_of_normal hCnorm hm hy) (isPGroup_pCoreOf' C)
    exact ⟨hQ hx, pCoreOf_le_self C hx⟩

theorem isPGroup_W : IsPGroup 2 ↥S.D.W := by
  intro w
  refine ⟨1, Subtype.ext ?_⟩
  simpa using S.D.sq w.2

theorem card_W_ge : 16 ≤ Nat.card ↥S.D.W := by
  have hn : 2 ≤ n := S.hyp.two_le
  have h1 := card_coreMod_mul_two (n := 2 * n + 1) (odd_two_mul_add_one n)
  have h2 : Nat.card ↥S.D.W = Nat.card ↥(coreMod (2 * n + 1)) := Nat.card_congr S.D.β.toEquiv
  have h3 : 2 ^ 5 ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize (2 : ℕ) ^ (2 * n + 1) = N at h1 h3
  norm_num at h3
  omega

theorem conj_W_of_mem_C {r w : G} (hr : r ∈ Subgroup.centralizer (X : Set G)) (hw : w ∈ S.D.W) :
    r * w * r⁻¹ = w := by
  have := Subgroup.mem_centralizer_iff.1 hr w (ModData.W_le_X S.D hw)
  rw [← this]
  group

theorem card_le_of_two_group_bound {B : ℕ}
    (hP : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card P ≤ B)
    {R : Subgroup G} (hRC : R ≤ Subgroup.centralizer (X : Set G)) (hR2 : IsPGroup 2 R) :
    16 * Nat.card R ≤ B := by
  classical
  have hRN : R ≤ Subgroup.normalizer (S.D.W : Set G) := fun r hr => by
    have hc : ∀ r' ∈ R, ∀ w ∈ S.D.W, r' * w * r'⁻¹ = w := fun r' hr' w hw =>
      S.conj_W_of_mem_C (hRC hr') hw
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by rw [hc r hr h hh]; exact hh, fun hh => ?_⟩
    have h1 := hc r⁻¹ (R.inv_mem hr) _ hh
    have e : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ = h := by group
    rw [e] at h1
    exact h1.symm ▸ hh
  have hP2 : IsPGroup 2 (S.D.W ⊔ R : Subgroup G) := S.isPGroup_W.to_sup_of_normal_left' hR2 hRN
  let f : ↥S.D.W × ↥R → ↥(S.D.W ⊔ R : Subgroup G) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨w, hw⟩, ⟨r, hr⟩⟩ ⟨⟨w', hw'⟩, ⟨r', hr'⟩⟩ h
    have h1 : w * r = w' * r' := congrArg Subtype.val h
    have h2 : w'⁻¹ * w = r' * r⁻¹ := by
      calc w'⁻¹ * w = w'⁻¹ * (w * r) * r⁻¹ := by group
        _ = w'⁻¹ * (w' * r') * r⁻¹ := by rw [h1]
        _ = r' * r⁻¹ := by group
    have hW : w'⁻¹ * w ∈ S.D.W := S.D.W.mul_mem (S.D.W.inv_mem hw') hw
    have hRt : w'⁻¹ * w ∈ R := h2 ▸ R.mul_mem hr' (R.inv_mem hr)
    have h3 : w'⁻¹ * w = 1 := S.D.fix S.hyp.two_le hW (fun x hx => by
      have := Subgroup.mem_centralizer_iff.1 (hRC hRt) x hx
      rw [this]
      group)
    have hww : w = w' := by
      calc w = w' * (w'⁻¹ * w) := by group
        _ = w' := by rw [h3, mul_one]
    subst hww
    have : r = r' := mul_left_cancel h1
    subst this
    rfl
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard
  have hB := hP _ hP2
  have h16 := S.card_W_ge
  nlinarith

theorem exists_not_comm_of_block : ∃ a b : G, a * b ≠ b * a :=
  STT.exists_noncomm_of_naturalAlt S.hyp.two_le S.hyp.nat

theorem tight_or_dihedral_plus (hE2 : SolomonTimmesfeldTight) (hE3a : WCBlockCentralizer)
    (hOrd : TightSmallGroupOrders) (hKP : KProper InCatalog G) :
    HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G ∨ TightDataPlus S := by
  classical
  have hn : 2 ≤ n := S.hyp.two_le
  by_cases hev : Even (Nat.card ↥(Subgroup.centralizer (X : Set G)))
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer (X : Set G))) := inferInstance
    have hN := S.normalizer_C_eq hev
    have hmax : IsMaximalTwoLocal
        (Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) := by
      rw [hN]; exact S.hyp.maxLocal
    have hF : Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer
          ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer
          ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)) := by
      rw [hN]; exact S.hyp.charTwo M S.hyp.maxLocal.1
    have h27 := hE2 G hKP S.hyp.simple S.exists_not_comm_of_block (Subgroup.centralizer (X : Set G))
      (S.tightlyEmbedded_C hev) hmax hF R
    have hRC : (R : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
        (Subgroup.centralizer (X : Set G)).subtype ≤ Subgroup.centralizer (X : Set G) :=
      Subgroup.map_subtype_le _
    have hR2 : IsPGroup 2 ((R : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
        (Subgroup.centralizer (X : Set G)).subtype) := R.isPGroup'.map _
    rcases h27 with ⟨hRO, hab, g₀, hg₀N, hg₀ne⟩ | ⟨-, hdih⟩ | ⟨hQ8, hgrp⟩ |
        ⟨⟨H, -, hHR, ⟨hHe⟩, -⟩, hL34⟩ | hSz | ⟨-, hel, h4, hTI6, hNR, hWC⟩
    ·
      right; right
      have hrOf : rOf M X = (R : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
          (Subgroup.centralizer (X : Set G)).subtype := S.rOf_eq_pCoreOf_C.trans hRO.symm
      have hTD : TightData S := by
        refine tightData_of_cor28 S ?_ ?_
        · intro r hr r' hr'
          rw [hrOf] at hr hr'
          exact comm_of_cyclic_or_elem hab r hr r' hr'
        · intro c hc hc2
          obtain ⟨j, hj⟩ := hc2
          rw [S.rOf_eq_pCoreOf_C]
          exact two_element_mem_of_sylow R hRO (Subgroup.mem_inf.1 hc).2 hj
      refine ⟨hTD, ?_, fun _ => ⟨g₀, ?_, ?_⟩⟩
      ·
        intro g hgM
        refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
        have hxR : x ∈ rOf M X := hx.1
        have hxg : g⁻¹ * x * g ∈ rOf M X := mem_conjSubgroup.1 hx.2
        have hodd : Odd (Nat.card ↥(Subgroup.centralizer (X : Set G) ⊓
            rightConjugate (Subgroup.centralizer (X : Set G)) g⁻¹)) :=
          (S.tightlyEmbedded_C hev).2 g⁻¹ (by
            rw [hN]
            intro h
            exact hgM (by simpa using M.inv_mem h))
        have hmem : x ∈ Subgroup.centralizer (X : Set G) ⊓
            rightConjugate (Subgroup.centralizer (X : Set G)) g⁻¹ :=
          ⟨hxR.2, (mem_rightConjugate_iff _ g⁻¹ x).2 (by simpa [inv_inv] using hxg.2)⟩
        obtain ⟨j, hj⟩ := isPGroup_pCoreOf' M ⟨x, hxR.1⟩
        exact eq_one_of_odd_card hodd hmem (j := j) (by simpa using congrArg Subtype.val hj)
      · rw [hrOf]
        rw [hN] at hg₀N
        exact hg₀N
      · rw [hrOf]
        exact hg₀ne
    ·
      exact hdih.elim Or.inl fun h => Or.inr (Or.inl h)
    ·
      exfalso
      have hb : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ 64 := by
        rcases hgrp with h | h | h | h | h
        · exact hOrd G (Or.inl h)
        · exact hOrd G (Or.inr (Or.inl h))
        · exact hOrd G (Or.inr (Or.inr (Or.inl h)))
        · exact hOrd G (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact hOrd G (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      have h16 := S.card_le_of_two_group_bound hb hRC hR2
      have hcard : Nat.card ↥((R : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
          (Subgroup.centralizer (X : Set G)).subtype) = 8 := by
        rw [Nat.card_congr hQ8.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      omega
    ·
      exfalso
      have hb : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ 64 :=
        hOrd G (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL34)))))
      have h16 := S.card_le_of_two_group_bound hb hRC hR2
      have hH16 : Nat.card ↥H = 16 := by
        rw [Nat.card_congr hHe.toEquiv, Nat.card_prod,
          Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4) ≃ ZMod 4), Nat.card_zmod]
      have hle := Subgroup.card_le_of_le hHR
      omega
    ·
      exfalso
      have hXC : X ≤ Subgroup.centralizer (((R : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
          (Subgroup.centralizer (X : Set G)).subtype : Subgroup G) : Set G) :=
        fun x hx r hr => (Subgroup.mem_centralizer_iff.1 (hRC hr) x hx).symm
      have hCsolv := STT.isSolvable_centralizer_of_stated_bender hSz hR2
        (STT.map_sylow_ne_bot hev R)
      have hXsolv : Group.IsSolvable ↥X :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXC)
      exact STT.not_isSolvable_of_naturalAlt hn S.hyp.nat hXsolv
    ·
      exfalso
      have hXC : X ≤ Subgroup.centralizer (((R : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
          (Subgroup.centralizer (X : Set G)).subtype : Subgroup G) : Set G) :=
        fun x hx r hr => (Subgroup.mem_centralizer_iff.1 (hRC hr) x hx).symm
      have hNRM : Subgroup.normalizer (((R : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
          (Subgroup.centralizer (X : Set G)).subtype : Subgroup G) : Set G) = M := by
        rw [hNR]; exact hN
      refine hE3a G S.hyp.simple S.hyp.charTwo _ X n hn hel h4 hTI6 ?_ ?_ ?_ ?_ ?_
        S.hyp.short S.hyp.nat hXC
      · rw [hNRM]; exact S.hyp.maxLocal
      · rw [hNRM]
        rw [hN] at hWC
        exact hWC
      · rw [hNRM]; exact S.hyp.unique
      · rw [hNRM]; exact S.hyp.le
      · rw [hNRM]; exact S.hyp.normal
  ·
    right; right
    have hodd : Odd (Nat.card ↥(Subgroup.centralizer (X : Set G))) := Nat.not_even_iff_odd.1 hev
    have h1 : ∀ r ∈ rOf M X, r = 1 := fun r hr => by
      obtain ⟨j, hj⟩ := isPGroup_pCoreOf' M ⟨r, hr.1⟩
      exact eq_one_of_odd_card hodd hr.2 (j := j) (by simpa using congrArg Subtype.val hj)
    have hRbot : rOf M X = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h1
    have hTD : TightData S := by
      refine tightData_of_cor28 S ?_ ?_
      · intro r hr r' hr'
        rw [h1 r hr, h1 r' hr']
      · intro c hc hc2
        obtain ⟨j, hj⟩ := hc2
        have := eq_one_of_odd_card hodd (Subgroup.mem_inf.1 hc).2 hj
        rw [this]
        exact (rOf M X).one_mem
    exact ⟨hTD, fun g _ => by rw [hRbot]; exact bot_inf_eq _, fun h => absurd hRbot h⟩

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
