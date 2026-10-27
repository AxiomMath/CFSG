module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltEnd
import CFSG.CGT.PushingUpLit.CGT6.EmbCbPerm

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.LocalCores CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp Equiv

variable {V : Type} [CommGroup V] [Finite V]

theorem EndCfg4.normalizes_of_subnormal {G T Y : Subgroup (MulAut V)} (h2 : Alt2Rank1)
    (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : YAlt Y m) {H : Subgroup (MulAut V)} (hHG : H ≤ G) (hYH : Y ≤ H)
    (hsub : (Y.subgroupOf H).IsSubnormal) : ∀ g ∈ H, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
  classical
  have hYG : Y ≤ G := fun _ hy => (h.adm.hYC hy).1
  have hqG : CFSG.Open.IsQuasisimple ↥(Y.subgroupOf G) := (h.std_of_YAlt hm hY).1
  have hqN : CFSG.IsQuasisimple ↥(Y.subgroupOf G) :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
      ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2 hqG)
  have hqY : CFSG.IsQuasisimple ↥Y :=
    isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYG) hqN
  have hK : IsComponent (Y.subgroupOf H) :=
    ⟨isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYH).symm hqY, hsub⟩
  intro g hg y hy
  let g' : ↥H := ⟨g, hg⟩
  let f : ↥H ≃* ↥H := MulAut.conj g'
  have hK' : IsComponent ((Y.subgroupOf H).map f.toMonoidHom) := isComponent_map_mulEquiv f hK
  rcases distinct_components_commute hK' hK with heq | hcomm
  · have hy' : (⟨y, hYH hy⟩ : ↥H) ∈ Y.subgroupOf H := hy
    have hmem : f ⟨y, hYH hy⟩ ∈ (Y.subgroupOf H).map f.toMonoidHom := ⟨_, hy', rfl⟩
    rw [heq] at hmem
    exact hmem
  · exfalso
    obtain ⟨ε⟩ := hY
    obtain ⟨a₁, a₂, ha1, ha2, ha1n, ha2n, ha12, hac⟩ := cbp_exists_comm_involutions m (by omega)
    obtain ⟨y₁, rfl⟩ := ε.surjective a₁
    obtain ⟨y₂, rfl⟩ := ε.surjective a₂
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hB : ∀ y : ↥Y, g * (y : MulAut V) * g⁻¹ ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
      intro y
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : (⟨z, hYH hz⟩ : ↥H) ∈ Y.subgroupOf H := hz
      have hmem : f ⟨y, hYH y.2⟩ ∈ (Y.subgroupOf H).map f.toMonoidHom :=
        ⟨_, show (⟨y, hYH y.2⟩ : ↥H) ∈ Y.subgroupOf H from y.2, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp (hcen hmem) _ hz'
      exact congrArg Subtype.val this
    have hpow : ∀ y : ↥Y, (y : MulAut V) ^ 2 = 1 → (g * (y : MulAut V) * g⁻¹) ^ 2 = 1 := by
      intro y hy
      rw [conj_pow, hy]
      group
    refine h2 V hV G T Y h m hm hodd ⟨ε⟩ (g * (y₁ : MulAut V) * g⁻¹) (g * (y₂ : MulAut V) * g⁻¹)
      ?_ ?_ (hB y₁) (hB y₂) (hpow y₁ ?_) (hpow y₂ ?_) ?_ ?_ ?_ ?_
    · exact G.mul_mem (G.mul_mem (hHG hg) (hYG y₁.2)) (G.inv_mem (hHG hg))
    · exact G.mul_mem (G.mul_mem (hHG hg) (hYG y₂.2)) (G.inv_mem (hHG hg))
    · have h : y₁ ^ 2 = 1 := ε.injective (by rw [map_pow, ha1, map_one])
      rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
    · have h : y₂ ^ 2 = 1 := ε.injective (by rw [map_pow, ha2, map_one])
      rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
    · intro hB1
      apply ha1n
      have : (y₁ : MulAut V) = 1 := by simpa using hB1
      have h1 : y₁ = 1 := Subtype.ext this
      rw [h1, map_one]
    · intro hB1
      apply ha2n
      have : (y₂ : MulAut V) = 1 := by simpa using hB1
      have h1 : y₂ = 1 := Subtype.ext this
      rw [h1, map_one]
    · intro hB1
      apply ha12
      have : (y₁ : MulAut V) = y₂ := by simpa using hB1
      have h1 : y₁ = y₂ := Subtype.ext this
      rw [h1]
    · have hy12 : y₁ * y₂ = y₂ * y₁ := ε.injective (by rw [map_mul, map_mul, hac])
      have : (y₁ : MulAut V) * y₂ = y₂ * y₁ := congrArg Subtype.val hy12
      calc g * (y₁ : MulAut V) * g⁻¹ * (g * (y₂ : MulAut V) * g⁻¹)
          = g * ((y₁ : MulAut V) * y₂) * g⁻¹ := by group
        _ = g * ((y₂ : MulAut V) * y₁) * g⁻¹ := by rw [this]
        _ = g * (y₂ : MulAut V) * g⁻¹ * (g * (y₁ : MulAut V) * g⁻¹) := by group

end CFSG.CGT.PushingUpLit.CGT6
