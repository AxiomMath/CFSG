module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IA5Perm
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614ICommon
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IIndex
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open Subgroup Equiv
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G} {x z : G}
  {H S K : Subgroup G}

structure A5Std (H S K : Subgroup G) (z : G) (f : ↥(K ⊔ S) →* Perm (Fin 5)) : Prop where
  surj : Function.Surjective f
  ker : ∀ y : ↥(K ⊔ S), f y = 1 ↔ (y : G) ∈ pCoreOf 2 H
  z_eq : ∀ hz : z ∈ K ⊔ S, f ⟨z, hz⟩ = cA

theorem z_mem_KS (h618 : Stage618 M H K z) : z ∈ K ⊔ S := mem_sup_left (z_mem_K h618)

theorem exists_a5Std (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) (hA : A5Case H S K) :
    ∃ f : ↥(K ⊔ S) →* Perm (Fin 5), A5Std H S K z f := by
  obtain ⟨f, hfs, hfk⟩ := hA
  have hzKS := z_mem_KS (S := S) h618
  set c := f ⟨z, hzKS⟩ with hc
  have hc3 : c ^ 3 = 1 := by
    rw [hc, ← map_pow]
    have : (⟨z, hzKS⟩ : ↥(K ⊔ S)) ^ 3 = 1 := Subtype.ext (by simpa using z_pow_three hyp)
    rw [this, map_one]
  have hc1 : c ≠ 1 := fun h1 => z_not_mem_core hyp ((hfk _).1 h1)
  obtain ⟨g, hg⟩ := exists_conj_cA c hc3 hc1
  refine ⟨(MulAut.conj g).toMonoidHom.comp f, ⟨(MulAut.conj g).surjective.comp hfs, fun y => ?_,
    fun hz => ?_⟩⟩
  · rw [← hfk y]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro h
      have := congrArg (fun a => g⁻¹ * a * g) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]
      group
  · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    exact hg

section Std

variable {f : ↥(K ⊔ S) →* Perm (Fin 5)}

theorem KS_le_H (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) : K ⊔ S ≤ H :=
  sup_le h618.comp.le (S_le_H hyp)

theorem A5Std.sign_K (h618 : Stage618 M H K z) {k : G} (hk : k ∈ K) :
    Perm.sign (f ⟨k, mem_sup_left hk⟩) = 1 := by
  set K' : Subgroup ↥(K ⊔ S) := K.subgroupOf (K ⊔ S)
  have hK' : ⁅K', K'⁆ = K' := by
    apply map_injective (subtype_injective (K ⊔ S))
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left]
    exact h618.comp.perfect
  have hle : K' ≤ (Perm.sign.comp f).ker := by
    rw [← hK']
    exact (commutator_mono le_top le_top).trans
      (Abelianization.commutator_subset_ker (Perm.sign.comp f))
  have hmem : (⟨k, mem_sup_left hk⟩ : ↥(K ⊔ S)) ∈ K' := hk
  exact hle hmem

theorem exists_mul_of_mem_KS (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) {y : G}
    (hy : y ∈ K ⊔ S) : ∃ k ∈ K, ∃ s ∈ S, y = k * s := by
  have hSK : S ≤ normalizer (K : Set G) := (S_le_H hyp).trans h618.comp.normal
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K S hSK] at hy
  obtain ⟨k, hk, s, hs, rfl⟩ := Set.mem_mul.1 hy
  exact ⟨k, hk, s, hs, rfl⟩

theorem pow_eight_S (hyp : Hyp P M x z H S) {s : G} (hs : s ∈ S) :
    f ⟨s, mem_sup_right hs⟩ ^ 8 = 1 := by
  obtain ⟨n, hn⟩ := isPGroup_S hyp ⟨s, hs⟩
  refine pow_eight_eq_one (k := n) ?_
  rw [← map_pow]
  have : (⟨s, mem_sup_right hs⟩ : ↥(K ⊔ S)) ^ 2 ^ n = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hn)
  rw [this, map_one]

theorem A5Std.conj_S (hf : A5Std H S K z f) (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    {s : G} (hs : s ∈ S) :
    cA * f ⟨s, mem_sup_right hs⟩ * cA⁻¹ =
      f ⟨z * s * z⁻¹, mem_sup_right ((mem_normalizer_iff.1 (z_mem_normalizer_S hyp) s).1 hs)⟩ := by
  rw [← hf.z_eq (z_mem_KS h618), ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem A5Std.eq_sA_of_sign (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) {s : G} (hs : s ∈ S)
    (hsg : Perm.sign (f ⟨s, mem_sup_right hs⟩) = -1) :
    f ⟨s, mem_sup_right hs⟩ = sA := by
  have hzs : z * s * z⁻¹ ∈ S := (mem_normalizer_iff.1 (z_mem_normalizer_S hyp) s).1 hs
  refine eq_sA_of_odd _ (pow_eight_S (f := f) hyp hs) hsg ?_
  rw [hf.conj_S hyp h618 hs, ← map_mul]
  exact pow_eight_S (f := f) hyp (S.mul_mem hs hzs)

theorem A5Std.exists_sA (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) : ∃ s, ∃ hs : s ∈ S, f ⟨s, mem_sup_right hs⟩ = sA := by
  by_contra hcon
  push Not at hcon
  have heven : ∀ s, ∀ hs : s ∈ S, Perm.sign (f ⟨s, mem_sup_right hs⟩) = 1 := by
    intro s hs
    rcases Int.units_eq_one_or (Perm.sign (f ⟨s, mem_sup_right hs⟩)) with h | h
    · exact h
    · exact (hcon s hs (hf.eq_sA_of_sign hyp h618 hs h)).elim
  obtain ⟨y, hy⟩ := hf.surj (swap 0 1)
  obtain ⟨k, hk, s, hs, hks⟩ := exists_mul_of_mem_KS hyp h618 y.2
  have hy' : y = ⟨k, mem_sup_left hk⟩ * ⟨s, mem_sup_right hs⟩ := Subtype.ext hks
  have := congrArg Perm.sign hy
  rw [hy', map_mul, map_mul, A5Std.sign_K h618 hk, heven s hs, sign_swap01] at this
  exact absurd this (by decide)

theorem A5Std.mem_or (hf : A5Std H S K z f) (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    {s : G} (hs : s ∈ S) : f ⟨s, mem_sup_right hs⟩ = 1 ∨ f ⟨s, mem_sup_right hs⟩ = sA := by
  rcases Int.units_eq_one_or (Perm.sign (f ⟨s, mem_sup_right hs⟩)) with h | h
  · left
    obtain ⟨s₁, hs₁, hs₁A⟩ := hf.exists_sA hyp h618
    have hss : s * s₁ ∈ S := S.mul_mem hs hs₁
    have hsg : Perm.sign (f ⟨s * s₁, mem_sup_right hss⟩) = -1 := by
      have e : (⟨s * s₁, mem_sup_right hss⟩ : ↥(K ⊔ S)) =
          ⟨s, mem_sup_right hs⟩ * ⟨s₁, mem_sup_right hs₁⟩ := rfl
      rw [e, map_mul, map_mul, h, hs₁A, sign_sA]
      rfl
    have h2 := hf.eq_sA_of_sign hyp h618 hss hsg
    have e : (⟨s * s₁, mem_sup_right hss⟩ : ↥(K ⊔ S)) =
        ⟨s, mem_sup_right hs⟩ * ⟨s₁, mem_sup_right hs₁⟩ := rfl
    rw [e, map_mul, hs₁A] at h2
    exact mul_right_cancel (h2.trans (one_mul sA).symm)
  · exact Or.inr (hf.eq_sA_of_sign hyp h618 hs h)

@[expose] noncomputable def a5X (S K : Subgroup G) (f : ↥(K ⊔ S) →* Perm (Fin 5)) :
    Subgroup G :=
  (stab01.comap f).map (K ⊔ S).subtype

theorem mem_a5X {y : G} : y ∈ a5X S K f ↔ ∃ hy : y ∈ K ⊔ S, f ⟨y, hy⟩ ∈ stab01 := by
  constructor
  · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
    exact ⟨hy, hmem⟩
  · rintro ⟨hy, hmem⟩
    exact ⟨⟨y, hy⟩, hmem, rfl⟩

theorem a5X_le_KS : a5X S K f ≤ K ⊔ S := map_subtype_le _

theorem a5X_le_H (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) : a5X S K f ≤ H :=
  a5X_le_KS.trans (KS_le_H hyp h618)

theorem A5Std.S_le_a5X (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) : S ≤ a5X S K f := by
  intro s hs
  refine mem_a5X.2 ⟨mem_sup_right hs, ?_⟩
  rcases hf.mem_or hyp h618 hs with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact sA_mem_stab01

theorem mem_a5X_of {y : ↥(K ⊔ S)} (hy : f y ∈ stab01) : (y : G) ∈ a5X S K f :=
  mem_a5X.2 ⟨y.2, hy⟩

theorem A5Std.pCoreOf_a5X (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) : pCoreOf 2 (a5X S K f) = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · intro w hw
    have hwX : w ∈ a5X S K f := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw
    obtain ⟨hwKS, hwst⟩ := mem_a5X.1 hwX
    have h2 : ∀ v ∈ pCoreOf 2 (a5X S K f), ∀ hv : v ∈ K ⊔ S, f ⟨v, hv⟩ ^ 8 = 1 := by
      intro v hv hvKS
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (a5X S K f) ⟨v, hv⟩
      refine pow_eight_eq_one (k := n) ?_
      rw [← map_pow]
      have : (⟨v, hvKS⟩ : ↥(K ⊔ S)) ^ 2 ^ n = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hn)
      rw [this, map_one]
    obtain ⟨y, hy⟩ := hf.surj dA
    have hyX : (y : G) ∈ a5X S K f := mem_a5X_of (by rw [hy]; exact dA_mem_stab01)
    have hyw : (y : G) * w * (y : G)⁻¹ ∈ pCoreOf 2 (a5X S K f) :=
      (mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hyX) w).1 hw
    have hprod := h2 _ (mul_mem hw hyw) (mul_mem hwKS (mul_mem (mul_mem y.2 hwKS) (inv_mem y.2)))
    have e : (⟨w * ((y : G) * w * (y : G)⁻¹),
        mul_mem hwKS (mul_mem (mul_mem y.2 hwKS) (inv_mem y.2))⟩ : ↥(K ⊔ S)) =
        ⟨w, hwKS⟩ * (y * ⟨w, hwKS⟩ * y⁻¹) := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, hy] at hprod
    have hfix := mem_stab01.1 hwst
    have h1 := eq_one_of_stab _ hfix.1 hfix.2 (h2 w hw hwKS) hprod
    exact (hf.ker ⟨w, hwKS⟩).1 h1
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((core_le_S hyp).trans (hf.S_le_a5X hyp h618)) ?_ (isPGroup_core hyp)
    exact (a5X_le_H hyp h618).trans (H_le_normalizer_core hyp)

theorem A5Std.charTwo_a5X (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) : CFSG.QuasithinUnique.CharTwo (a5X S K f) := by
  unfold CFSG.QuasithinUnique.CharTwo
  rw [hf.pCoreOf_a5X hyp h618]
  exact (inf_le_inf_right _ (a5X_le_H hyp h618)).trans (charTwo_H hyp)

noncomputable def a5Theta (S K : Subgroup G) (f : ↥(K ⊔ S) →* Perm (Fin 5)) :
    ↥(a5X S K f) →* ↥stab01 :=
  (f.comp (inclusion a5X_le_KS)).codRestrict stab01 (by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact hy)

noncomputable def a5Psi (S K : Subgroup G) (f : ↥(K ⊔ S) →* Perm (Fin 5)) :
    ↥(a5X S K f) →* Perm (Fin 3) :=
  stab01Equiv.toMonoidHom.comp (a5Theta S K f)

theorem A5Std.a5Psi_surjective (hf : A5Std H S K z f) : Function.Surjective (a5Psi S K f) := by
  intro π
  obtain ⟨y, hy⟩ := hf.surj (stab01Equiv.symm π : Perm (Fin 5))
  refine ⟨⟨y, mem_a5X_of (by rw [hy]; exact (stab01Equiv.symm π).2)⟩, ?_⟩
  change stab01Equiv (a5Theta S K f _) = π
  have : a5Theta S K f ⟨y, mem_a5X_of (by rw [hy]; exact (stab01Equiv.symm π).2)⟩ =
      stab01Equiv.symm π := Subtype.ext hy
  rw [this, MulEquiv.apply_symm_apply]

theorem A5Std.mem_ker_a5Psi (hf : A5Std H S K z f) (y : ↥(a5X S K f)) :
    a5Psi S K f y = 1 ↔ (y : G) ∈ pCoreOf 2 H := by
  change stab01Equiv (a5Theta S K f y) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  change (⟨f (inclusion a5X_le_KS y), _⟩ : ↥stab01) = 1 ↔ _
  rw [Subtype.ext_iff]
  exact hf.ker _

theorem A5Std.ker_a5Psi (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) : (a5Psi S K f).ker = CFSG.Open.pCore 2 ↥(a5X S K f) := by
  have h := hf.pCoreOf_a5X hyp h618
  ext y
  rw [MonoidHom.mem_ker, hf.mem_ker_a5Psi, ← h]
  change _ ↔ y ∈ CFSG.Open.pCore 2 ↥(a5X S K f)
  constructor
  · rintro ⟨y', hy', hyy⟩
    rwa [← Subtype.ext hyy]
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem A5Std.nonempty_equiv (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) :
    Nonempty (CFSG.Quasithin.OTwoQuot (a5X S K f) ≃* Perm (Fin 3)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (hf.ker_a5Psi hyp h618).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hf.a5Psi_surjective)⟩

theorem A5Std.relIndex_core_S (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) : (pCoreOf 2 H).relIndex S = 2 := by
  obtain ⟨s₁, hs₁, hs₁A⟩ := hf.exists_sA hyp h618
  rw [relIndex, index_eq_two_iff]
  refine ⟨⟨s₁, hs₁⟩, fun b => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf]
  have hb := hf.mem_or hyp h618 b.2
  have e : (⟨((b * ⟨s₁, hs₁⟩ : ↥S) : G), mem_sup_right (b * ⟨s₁, hs₁⟩).2⟩ : ↥(K ⊔ S)) =
      ⟨b, mem_sup_right b.2⟩ * ⟨s₁, mem_sup_right hs₁⟩ := rfl
  rw [← hf.ker ⟨b, mem_sup_right b.2⟩, ← hf.ker ⟨_, mem_sup_right (b * ⟨s₁, hs₁⟩).2⟩, e,
    map_mul, hs₁A]
  rcases hb with h | h
  · rw [h, one_mul]
    exact Or.inr ⟨rfl, sA_ne_one⟩
  · rw [h]
    refine Or.inl ⟨by decide, fun h' => sA_ne_one h'⟩

theorem A5Std.isSylowTwoOf (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) : CFSG.QuasithinUnique.IsSylowTwoOf S (a5X S K f) := by
  refine ⟨hf.S_le_a5X hyp h618, isPGroup_S hyp, ?_⟩
  have hX : Nat.card ↥(a5X S K f) = Nat.card ↥(pCoreOf 2 H) * 6 := by
    have h1 := card_mul_index (a5Psi S K f).ker
    rw [index_ker, MonoidHom.range_eq_top.2 hf.a5Psi_surjective, card_top, Nat.card_perm,
      Nat.card_fin] at h1
    have h2 : Nat.card ↥(a5Psi S K f).ker = Nat.card ↥(pCoreOf 2 H) := by
      have hk : (a5Psi S K f).ker = (pCoreOf 2 H).subgroupOf (a5X S K f) := by
        ext y
        rw [MonoidHom.mem_ker, hf.mem_ker_a5Psi, mem_subgroupOf]
      rw [hk]
      exact Nat.card_congr (subgroupOfEquivOfLe
        ((core_le_S hyp).trans (hf.S_le_a5X hyp h618))).toEquiv
    rw [← h1, h2]
    rfl
  have hS : Nat.card ↥S = Nat.card ↥(pCoreOf 2 H) * 2 := by
    have := relIndex_mul_card (pCoreOf 2 H) S
    rw [hf.relIndex_core_S hyp h618, inf_eq_left.2 (core_le_S hyp)] at this
    omega
  have hrel := relIndex_mul_card S (a5X S K f)
  rw [inf_eq_left.2 (hf.S_le_a5X hyp h618), hS, hX] at hrel
  have hpos : 0 < Nat.card ↥(pCoreOf 2 H) := Nat.card_pos
  have h3 : S.relIndex (a5X S K f) = 3 := by
    have : S.relIndex (a5X S K f) * 2 = 6 :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [← hrel]; ring)
    omega
  change ¬ 2 ∣ S.relIndex (a5X S K f)
  rw [h3]
  decide

theorem A5Std.false_of_char (hf : A5Std H S K z f) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) {C : Subgroup G} (hCS : C ≤ S) (hC1 : C ≠ ⊥)
    (hCchar : (C.subgroupOf S).Characteristic) (hXC : a5X S K f ≤ normalizer (C : Set G)) :
    False := by
  have hCM : normalizer (C : Set G) ≤ M := hyp.optimal.char_le C hCS hC1 hCchar
  set L : Subgroup (Perm (Fin 5)) := ((normalizer (C : Set G)).subgroupOf (K ⊔ S)).map f
  have hmem : ∀ σ ∈ stab01, σ ∈ L := by
    intro σ hσ
    obtain ⟨y, hy⟩ := hf.surj σ
    exact ⟨y, hXC (mem_a5X_of (by rw [hy]; exact hσ)), hy⟩
  have hcL : cA ∈ L := ⟨⟨z, z_mem_KS h618⟩,
    normalizer_le_normalizer_of_char hCS hCchar (z_mem_normalizer_S hyp),
    hf.z_eq (z_mem_KS h618)⟩
  have hL : L = ⊤ := eq_top_of_mem hcL (hmem dA dA_mem_stab01) (hmem sA sA_mem_stab01)
  refine h618.comp.not_le fun k hk => ?_
  obtain ⟨y, hyC, hyk⟩ := (hL ▸ mem_top (f ⟨k, mem_sup_left hk⟩) : f ⟨k, mem_sup_left hk⟩ ∈ L)
  have h1 : f (y⁻¹ * ⟨k, mem_sup_left hk⟩) = 1 := by rw [map_mul, map_inv, hyk, inv_mul_cancel]
  have h2 : (y : G)⁻¹ * k ∈ M := core_le_M hyp ((hf.ker _).1 h1)
  have h3 : (y : G) ∈ M := hCM hyC
  simpa using M.mul_mem h3 h2

theorem A5Std.card_commutator (h283 : GL83.I_28_3_S3) (hf : A5Std H S K z f)
    (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) :
    Nat.card ↥⁅pCoreOf 2 H, zpowers z⁆ = 4 := by
  rcases h283 G (a5X S K f) S (hf.isSylowTwoOf hyp h618) (hf.charTwo_a5X hyp h618)
      (hf.nonempty_equiv hyp h618) with ⟨C, hCS, hC1, hCchar, hXC⟩ | hu
  · exact (hf.false_of_char hyp h618 hCS hC1 hCchar hXC).elim
  obtain ⟨y, hy⟩ := hf.surj gA
  set u : G := (y : G) * z * (y : G)⁻¹ with hu_def
  have huKS : u ∈ K ⊔ S := mul_mem (mul_mem y.2 (z_mem_KS h618)) (inv_mem y.2)
  have hfu : f ⟨u, huKS⟩ = dA := by
    have e : (⟨u, huKS⟩ : ↥(K ⊔ S)) = y * ⟨z, z_mem_KS h618⟩ * y⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hy, hf.z_eq, gA_conj]
  have huX : u ∈ a5X S K f := mem_a5X.2 ⟨huKS, by rw [hfu]; exact dA_mem_stab01⟩
  have hu3 : u ^ 3 = 1 := by rw [hu_def, conj_pow, z_pow_three hyp]; group
  have hu1 : u ≠ 1 := fun h1 => z_ne_one hyp (conj_eq_one_iff.1 h1)
  have h4 := (hu u huX hu3 hu1).1
  rw [hf.pCoreOf_a5X hyp h618] at h4
  have hyH : (y : G) ∈ normalizer (pCoreOf 2 H : Set G) :=
    H_le_normalizer_core hyp (KS_le_H hyp h618 y.2)
  have hmap : ⁅pCoreOf 2 H, zpowers u⁆ =
      (⁅pCoreOf 2 H, zpowers z⁆).map (MulAut.conj (y : G)).toMonoidHom := by
    have hO : (pCoreOf 2 H).map (MulAut.conj (y : G)).toMonoidHom = pCoreOf 2 H :=
      mem_normalizer_iff_map_conj_eq.1 hyH
    rw [map_commutator, hO, MonoidHom.map_zpowers]
    rfl
  rw [hmap, card_map_of_injective (MulAut.conj (y : G)).injective] at h4
  exact h4

end Std

theorem stage620iii_of_a5Case (h283 : GL83.I_28_3_S3) (hyp : Hyp P M x z H S)
    (h618 : Stage618 M H K z) (hA : A5Case H S K) : Stage620iii H S z := by
  obtain ⟨f, hf⟩ := exists_a5Std hyp h618 hA
  have hcore : (centralizer ({z} : Set G)).relIndex (pCoreOf 2 H) = 4 :=
    relIndex_centralizer_eq_four (isPGroup_core hyp) (z_pow_three hyp)
      (H_le_normalizer_core hyp (z_mem_H hyp)) (exists_core_not_comm hyp)
      (hf.card_commutator h283 hyp h618).le
  refine ⟨by rw [centralizer_zpowers_eq]; exact hcore, ?_⟩
  rw [centralizer_zpowers_eq]
  calc (centralizer ({z} : Set G)).relIndex S
      ≤ (centralizer ({z} : Set G)).relIndex (pCoreOf 2 H) * (pCoreOf 2 H).relIndex S :=
        relIndex_centralizer_le_mul z (core_le_S hyp)
    _ = 4 * 2 := by rw [hcore, hf.relIndex_core_S hyp h618]
    _ ≤ 16 := by norm_num

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
