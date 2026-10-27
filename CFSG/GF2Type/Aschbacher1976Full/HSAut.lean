module

public import CFSG.GF2Type.Aschbacher1976Full.HSAutBasic
public import CFSG.GF2Type.Aschbacher1976Full.HSAutLinear
public import CFSG.GF2Type.Aschbacher1976Full.HSInterfaces

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

theorem hsAut_surj (hGL : GL3Stmt) (hset : HSSetting G z) (hV : HSV z T V) :
    Function.Surjective (actV V) := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  have hcomm : ∀ a b : ↥V, a * b = b * a :=
    fun a b => Subtype.ext (hsAut_mul_comm hV a.2 b.2)
  have hsq : ∀ a : ↥V, a * a = 1 := fun a => Subtype.ext (hsAut_mul_self hV a.2)
  obtain ⟨h168, hX⟩ := hGL hV.card_eq hcomm hsq
  have h14 : 14 ∣ Nat.card (actV V).range := by
    have h7 := hsAut_seven_dvd hz hV
    have h2 := hsAut_two_dvd hset hV
    omega
  have htop : (actV V).range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ ((hX _ h14).trans h168.symm)
  exact MonoidHom.range_eq_top.mp htop

theorem hsAut_card (hGL : GL3Stmt) (hset : HSSetting G z) (hV : HSV z T V) :
    Nat.card (Subgroup.normalizer (V : Set G)) =
      168 * Nat.card (Subgroup.centralizer (V : Set G)) := by
  have hcomm : ∀ a b : ↥V, a * b = b * a :=
    fun a b => Subtype.ext (hsAut_mul_comm hV a.2 b.2)
  have hsq : ∀ a : ↥V, a * a = 1 := fun a => Subtype.ext (hsAut_mul_self hV a.2)
  have h168 := (hGL hV.card_eq hcomm hsq).1
  have h1 := Subgroup.card_ker_mul_card_of_surjective (hsAut_surj hGL hset hV)
  rw [h168, actV_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv]
    at h1
  rw [← h1]
  ring

theorem hsAut_index (hGL : GL3Stmt) (hset : HSSetting G z) (hV : HSV z T V) :
    ((Subgroup.centralizer (V : Set G)).subgroupOf
      (Subgroup.normalizer (V : Set G))).index = 168 := by
  have hcomm : ∀ a b : ↥V, a * b = b * a :=
    fun a b => Subtype.ext (hsAut_mul_comm hV a.2 b.2)
  have hsq : ∀ a : ↥V, a * a = 1 := fun a => Subtype.ext (hsAut_mul_self hV a.2)
  rw [← actV_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (hsAut_surj hGL hset hV),
    Subgroup.card_top]
  exact (hGL hV.card_eq hcomm hsq).1

theorem hsAut_transitive (hGL : GL3Stmt) (hset : HSSetting G z) (hV : HSV z T V) {v v' : G}
    (hv : v ∈ V) (hv' : v' ∈ V) (hvz : v ∉ Subgroup.zpowers z)
    (hv'z : v' ∉ Subgroup.zpowers z) :
    ∃ n : G, n ∈ Hz z ∧ n ∈ Subgroup.normalizer (V : Set G) ∧ n * v * n⁻¹ = v' := by
  have hz : orderOf z = 2 := hset.1.2.2.1
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hcomm : ∀ a b : ↥V, a * b = b * a :=
    fun a b => Subtype.ext (hsAut_mul_comm hV a.2 b.2)
  have hsq : ∀ a : ↥V, a * a = 1 := fun a => Subtype.ext (hsAut_mul_self hV a.2)
  let z0 : ↥V := ⟨z, hV.z_mem⟩
  have hnot : ∀ {u : G} (hu : u ∈ V), u ∉ Subgroup.zpowers z →
      (⟨u, hu⟩ : ↥V) ∉ Subgroup.zpowers z0 := by
    intro u hu hnu hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hnu
    have h1 : z ^ k = u := congrArg Subtype.val hk
    exact h1 ▸ Subgroup.zpow_mem_zpowers z k
  obtain ⟨σ, hσ1, hσ2⟩ := hsAut_exists_mulAut_pair hV.card_eq hcomm hsq
    (a := z0) (b := ⟨v, hv⟩) (a' := z0) (b' := ⟨v', hv'⟩)
    (fun h => hz1 (congrArg Subtype.val h)) (fun h => hz1 (congrArg Subtype.val h))
    (hnot hv hvz) (hnot hv' hv'z)
  obtain ⟨⟨n, hnN⟩, hnσ⟩ := hsAut_surj hGL hset hV σ
  have h1 : n * z * n⁻¹ = z := by
    have := congrArg (fun τ : MulAut ↥V => ((τ z0 : ↥V) : G)) hnσ
    simp only [actV_apply, hσ1] at this
    exact this
  have h2 : n * v * n⁻¹ = v' := by
    have := congrArg (fun τ : MulAut ↥V => ((τ ⟨v, hv⟩ : ↥V) : G)) hnσ
    simp only [actV_apply, hσ2] at this
    exact this
  exact ⟨n, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1), hnN, h2⟩

end CFSG.GF2Type.Aschbacher1976Full.HS
