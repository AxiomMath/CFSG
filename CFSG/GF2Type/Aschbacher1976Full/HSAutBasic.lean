module

public import CFSG.GF2Type.Aschbacher1976Full.WidthStruct
public import CFSG.GF2Type.Aschbacher1976Full.HSVDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

section Action

variable {G : Type} [Group G] {V : Subgroup G}

@[expose] noncomputable def actV (V : Subgroup G) :
    ↥(Subgroup.normalizer (V : Set G)) →* MulAut ↥V :=
  V.normalizerMonoidHom

theorem actV_apply (n : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    ((actV V n v : ↥V) : G) = (n : G) * (v : G) * (n : G)⁻¹ :=
  V.normalizerMonoidHom_apply_apply_coe n v

theorem actV_ker : (actV V).ker =
    (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G)) :=
  V.normalizerMonoidHom_ker

end Action

section Basic

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

theorem hsAut_mul_comm (hV : HSV z T V) {a b : G} (ha : a ∈ V) (hb : b ∈ V) :
    a * b = b * a := by
  have := hV.isElem.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : V) ⟨b, hb⟩)

theorem hsAut_mul_self (hV : HSV z T V) {a : G} (ha : a ∈ V) : a * a = 1 := by
  have := hV.isElem.2 a ha
  rwa [pow_two] at this

theorem hsAut_T_le_normalizer (hV : HSV z T V) : T ≤ Subgroup.normalizer (V : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hV.normal_in_T t ht h hh, fun hh => ?_⟩
  have := hV.normal_in_T t⁻¹ (T.inv_mem ht) _ hh
  simpa [mul_assoc] using this

theorem hsAut_exists_not_mem_zpowers (hz : orderOf z = 2) (hV : HSV z T V) :
    ∃ v ∈ V, v ∉ Subgroup.zpowers z := by
  by_contra h
  have hle : V ≤ Subgroup.zpowers z := fun v hv => not_not.mp fun hn => h ⟨v, hv, hn⟩
  have := Subgroup.card_le_of_le hle
  rw [hV.card_eq, Nat.card_zpowers, hz] at this
  omega

theorem hsAut_orbit_eq (hz : orderOf z = 2) (hV : HSV z T V) :
    MulAction.orbit (actV V).range (⟨z, hV.z_mem⟩ : ↥V) = {w | w ≠ 1} := by
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  ext w
  simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨σ, hσ⟩, hσw⟩ h1
    have h2 : σ ⟨z, hV.z_mem⟩ = 1 := hσw.trans h1
    exact hz1 (congrArg Subtype.val ((MulEquiv.map_eq_one_iff σ).mp h2))
  · intro hw
    obtain ⟨n, hn, hnz⟩ := hV.trans (w : G) w.2 (fun h => hw (Subtype.ext h))
    refine ⟨⟨actV V ⟨n, hn⟩, ⟨_, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show ((actV V ⟨n, hn⟩ ⟨z, hV.z_mem⟩ : ↥V) : G) = w
    rw [actV_apply]
    exact hnz

theorem hsAut_seven_dvd (hz : orderOf z = 2) (hV : HSV z T V) :
    7 ∣ Nat.card (actV V).range := by
  have hcard : (MulAction.orbit (actV V).range (⟨z, hV.z_mem⟩ : ↥V)).ncard = 7 := by
    rw [hsAut_orbit_eq hz hV]
    have : {w : ↥V | w ≠ 1} = Set.univ \ {1} := by ext; simp
    rw [this, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hV.card_eq]
  have hdvd := Subgroup.index_dvd_card
    (MulAction.stabilizer (actV V).range (⟨z, hV.z_mem⟩ : ↥V))
  rwa [MulAction.index_stabilizer, hcard] at hdvd

theorem hsAut_two_dvd (hset : HSSetting G z) (hV : HSV z T V) :
    2 ∣ Nat.card (actV V).range := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  obtain ⟨v, hvV, hvz⟩ := hsAut_exists_not_mem_zpowers hz hV
  have hv1 : v ≠ 1 := fun h => hvz (h ▸ Subgroup.one_mem _)
  have hvF : v ∈ Fz z := hV.le_F hvV
  obtain ⟨f, hfA, hf⟩ : ∃ f ∈ A, v * f ≠ f * v := by
    by_contra hcon
    have hcomm : ∀ b ∈ A, v * b = b * v := fun b hb => not_not.mp fun h => hcon ⟨b, hb, h⟩
    have hvZ : v ∈ Z := Width.mem_Z_of_comm hD hz hvF hcomm
    have hvsq : v ^ 2 = 1 := by rw [pow_two]; exact hsAut_mul_self hV hvV
    exact hvz (Width.involution_eq hD hz hvZ hvsq hv1 ▸ Subgroup.mem_zpowers z)
  have hfF : f ∈ Fz z := hD.sup_eq ▸ Subgroup.mem_sup_right hfA
  have hfN : f ∈ Subgroup.normalizer (V : Set G) := hsAut_T_le_normalizer hV (hV.F_le_T hfF)
  let ψf : MulAut ↥V := actV V ⟨f, hfN⟩
  have hne : ψf ≠ 1 := by
    intro h
    apply hf
    have h1 : ((ψf ⟨v, hvV⟩ : ↥V) : G) = v := by rw [h]; rfl
    rw [show ψf ⟨v, hvV⟩ = actV V ⟨f, hfN⟩ ⟨v, hvV⟩ from rfl, actV_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hsq : ψf ^ 2 = 1 := by
    rw [pow_two]
    ext u
    show ((ψf (ψf u) : ↥V) : G) = u
    rw [show ψf (ψf u) = actV V ⟨f, hfN⟩ (actV V ⟨f, hfN⟩ u) from rfl, actV_apply, actV_apply]
    have h3 : f * (f * (u : G) * f⁻¹) * f⁻¹ = (f * f) * u * (f * f)⁻¹ := by group
    rw [h3]
    rcases Width.sq_F hD hz hfF with h4 | h4
    · rw [← pow_two, h4]; simp
    · rw [← pow_two, h4]
      exact mul_inv_eq_iff_eq_mul.mpr (hsAut_mul_comm hV hV.z_mem u.2)
  have hord : orderOf ψf = 2 := orderOf_eq_prime hsq hne
  have hle : Subgroup.zpowers ψf ≤ (actV V).range := Subgroup.zpowers_le.mpr ⟨_, rfl⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, hord] at hdvd

end Basic

end CFSG.GF2Type.Aschbacher1976Full.HS
