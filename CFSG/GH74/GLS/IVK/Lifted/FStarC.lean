module

public import CFSG.GH74.GLS.IVK.Lifted.Lem13a52
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct5

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

section FStar

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem comm_mul_right_aux (k c₁ c₂ : G) :
    ⁅k, c₁ * c₂⁆ = ⁅k, c₁⁆ * (c₁ * ⁅k, c₂⁆ * c₁⁻¹) := by
  simp only [commutatorElement_def]
  group

omit [Finite G] in
@[expose] def centBarSub (z : G) (K : Subgroup G) : Subgroup G where
  carrier := {c | c ∈ Cz z ∧ ∀ k ∈ K, ⁅k, c⁆ ∈ Oz z}
  one_mem' := ⟨one_mem _, fun k _ => by simp⟩
  mul_mem' := by
    rintro c₁ c₂ ⟨hc₁C, hc₁⟩ ⟨hc₂C, hc₂⟩
    refine ⟨mul_mem hc₁C hc₂C, fun k hk => ?_⟩
    rw [comm_mul_right_aux]
    exact (Oz z).mul_mem (hc₁ k hk) (Oz_conj hc₁C (hc₂ k hk))
  inv_mem' := by
    rintro c ⟨hcC, hc⟩
    refine ⟨inv_mem hcC, fun k hk => ?_⟩
    have e : ⁅k, c⁻¹⁆ = c⁻¹ * (⁅k, c⁆)⁻¹ * c⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Oz_conj (inv_mem hcC) ((Oz z).inv_mem (hc k hk))

omit [Finite G] in
theorem z_mem_centBarSub {K : Subgroup G} (hK : K ≤ Cz z) : z ∈ centBarSub z K := by
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, fun k hk => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 (hK hk))]
  exact (Oz z).one_mem

variable {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop}

omit [Finite G] in
theorem centBarSub_conj (hM : M.M4 (pPrimeCoreOf 2) FA SD z S K₁ K₂) {x c : G} (hx : x ∈ Cz z)
    (hc : c ∈ centBarSub z (K₁ ⊔ K₂)) : x * c * x⁻¹ ∈ centBarSub z (K₁ ⊔ K₂) := by
  obtain ⟨hcC, hc⟩ := hc
  refine ⟨mul_mem (mul_mem hx hcC) (inv_mem hx), fun k hk => ?_⟩
  have e : ⁅k, x * c * x⁻¹⁆ = x * ⁅x⁻¹ * k * x, c⁆ * x⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Oz_conj hx (hc _ (hM.C_norm_K' hx hk))

omit [Finite G] in
theorem mem_normalizer_centBarSub (hM : M.M4 (pPrimeCoreOf 2) FA SD z S K₁ K₂) {x : G}
    (hx : x ∈ Cz z) : x ∈ normalizer (centBarSub z (K₁ ⊔ K₂) : Set G) :=
  M.mem_normalizer_of_both (fun _ hc => centBarSub_conj hM hx hc)
    (fun _ hc => by simpa using centBarSub_conj hM (inv_mem hx) hc)

theorem centBarSub_fix (hM : M.M4 (pPrimeCoreOf 2) FA SD z S K₁ K₂) (hpc₁ : IsPCompIn 2 (Cz z) K₁)
    {s : G} (hs : s ∈ centBarSub z (K₁ ⊔ K₂)) : M.cj K₁ s = K₁ ∧ M.cj K₂ s = K₂ := by
  rcases hM.perm s hs.1 with h | ⟨h1, h2⟩
  · exact h
  exfalso
  obtain ⟨a, ha, b, hb, hab⟩ := hM.nonab K₁ (Or.inl rfl)
  apply hab
  have hb' : s * b * s⁻¹ ∈ K₂ := by
    have : b ∈ M.cj K₂ s := by rw [h2]; exact hb
    exact M.mem_cj.1 this
  obtain ⟨m, hm_def⟩ : ∃ m : G, m = ⁅b, s⁆ := ⟨_, rfl⟩
  have hm : m ∈ Oz z := by
    rw [hm_def]
    exact hs.2 b (mem_sup_left hb)
  have hmC : m ∈ Cz z := TwoThin.pPrimeCoreOf_le (Cz z) hm
  have hbm : b = m * (s * b * s⁻¹) := by
    rw [hm_def]
    simp only [commutatorElement_def]
    group
  have e := comm_mul_right_aux a m (s * b * s⁻¹)
  rw [← hbm] at e
  have h3 : ⁅a, b⁆ ∈ Oz z := by
    rw [e]
    refine (Oz z).mul_mem ?_ (Oz_conj hmC (pPrimeCoreOf_le_Oz hpc₁ ((hM.cs₁ hb').2.2 a ha)))
    rw [commutatorElement_def]
    exact (Oz z).mul_mem (Oz_conj (hpc₁.1 ha) hm) ((Oz z).inv_mem hm)
  refine inf_Oz_le hpc₁ ⟨?_, h3⟩
  rw [commutatorElement_def]
  exact K₁.mul_mem (K₁.mul_mem (K₁.mul_mem ha hb) (K₁.inv_mem ha)) (K₁.inv_mem hb)

end FStar

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem inf_centBarSub_le (hII : II4_4_4_center) (hstd : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z) :
    S ⊓ centBarSub z (K₁ ⊔ K₂) ≤ zpowers z := by
  intro s hs
  have hM := m4_of_std hII hstd
  have hK₁m : K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert _ _
  have hK₂m : K₂ ∈ ({K₁, K₂} : Set (Subgroup G)) := Set.mem_insert_of_mem _ rfl
  have hpc₁ : IsPCompIn 2 (Cz z) K₁ := rigid_isPCompIn (std4_comp_rigid hstd hK₁m)
  have hpc₂ : IsPCompIn 2 (Cz z) K₂ := rigid_isPCompIn (std4_comp_rigid hstd hK₂m)
  obtain ⟨hf₁, hf₂⟩ := centBarSub_fix hM hpc₁ hs.2
  have hsC : s ∈ Cz z := hs.2.1
  have key : ∀ {K : Subgroup G}, IsPCompIn 2 (Cz z) K → M.cj K s = K → (K = K₁ ∨ K = K₂) →
      ∀ x ∈ K, ⁅x, s⁆ ∈ pPrimeCoreOf 2 (K₁ ⊔ K₂) := by
    intro K hpc hfix hKK x hx
    have hx' : s * x⁻¹ * s⁻¹ ∈ K := by
      have : x⁻¹ ∈ M.cj K s := by rw [hfix]; exact K.inv_mem hx
      exact M.mem_cj.1 this
    have hxs : ⁅x, s⁆ ∈ K := by
      have e : ⁅x, s⁆ = x * (s * x⁻¹ * s⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact K.mul_mem hx hx'
    have hxO : ⁅x, s⁆ ∈ Oz z := hs.2.2 x (hM.comp_le hKK hx)
    exact hM.O_le_OK hKK (inf_Oz_le hpc ⟨hxs, hxO⟩)
  have hsec := hM.secCent_of_gen hsC (key hpc₁ hf₁ (Or.inl rfl)) (key hpc₂ hf₂ (Or.inr rfl))
  have hmem : s ∈ Qz S z := by
    rw [Qz_eq hstd]
    exact Subgroup.mem_inf.2 ⟨hs.1, hsec⟩
  rwa [hQ] at hmem

theorem centBarSub_le_sup (hII : II4_4_4_center) (hstd : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z) :
    centBarSub z (K₁ ⊔ K₂) ≤ zpowers z ⊔ Oz z := by
  classical
  have hM := m4_of_std hII hstd
  set N : Subgroup G := centBarSub z (K₁ ⊔ K₂) with hN
  have hNC : N ≤ Cz z := fun c hc => hc.1
  have hCN : ∀ x ∈ Cz z, x ∈ normalizer (N : Set G) := fun x hx => mem_normalizer_centBarSub hM hx
  have hzS : z ∈ S := by
    have : z ∈ Qz S z := by
      rw [hQ]
      exact mem_zpowers z
    exact this.1
  have hzN : zpowers z ≤ N := zpowers_le.2 (z_mem_centBarSub hM.K_le_C)
  have hSN : S ⊓ N = zpowers z :=
    le_antisymm (inf_centBarSub_le hII hstd hQ) (le_inf (zpowers_le.2 hzS) hzN)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (zpowers z) N := by
    rw [← hSN]
    exact hstd.sylow.inf_of_le_normalizer hNC (fun x hx => hCN x hx)
  obtain ⟨P2, hP2⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hP2card : Nat.card ↥P2 = 2 := by
    have h1 : Nat.card ↥(P2 : Subgroup ↥N) = Nat.card ↥((zpowers z).subgroupOf N) := by
      rw [hP2]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzN).toEquiv,
      M.card_zpowers_of_sq hM.z_sq hM.z_ne] at h1
    exact h1
  have hP2c : IsCyclic ↥P2 := isCyclic_of_prime_card hP2card
  obtain ⟨-, hmul, -, -, -⟩ := CFSG.cyclic_sylow_normal_odd_complement P2 hP2c
  set M' : Subgroup G := pPrimeCoreOf 2 N with hM'
  have hM'N : M' ≤ N := TwoThin.pPrimeCoreOf_le N
  have hM'O : M' ≤ Oz z :=
    le_pPrimeCoreOf' (hM'N.trans hNC)
      (fun x hx m hm => TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (hCN x hx) hm)
      (TwoThin.card_pPrimeCoreOf_odd N)
  intro c hc
  have hcmem : (⟨c, hc⟩ : ↥N) ∈ (Set.univ : Set ↥N) := Set.mem_univ _
  rw [← hmul] at hcmem
  obtain ⟨k, hk, w, hw, hkw⟩ := Set.mem_mul.1 hcmem
  have hck : c = (k : G) * (w : G) := by
    have := congrArg Subtype.val hkw
    simpa using this.symm
  have hkM : (k : G) ∈ M' := Subgroup.mem_map_of_mem N.subtype hk
  have hwz : (w : G) ∈ zpowers z := by
    have : w ∈ (P2 : Subgroup ↥N) := hw
    rw [hP2] at this
    exact Subgroup.mem_subgroupOf.1 this
  rw [hck]
  exact (zpowers z ⊔ Oz z).mul_mem (mem_sup_right (hM'O hkM)) (mem_sup_left hwz)

theorem fStar_C_of_II4 (hII : II4_4_4_center) : FStar_C := by
  intro G _ _ z S K₁ K₂ hstd hQ c hc hcomm
  exact centBarSub_le_sup hII hstd hQ ⟨hc, hcomm⟩

end Main

end CFSG.GH74.GLS.IVK.Lifted
