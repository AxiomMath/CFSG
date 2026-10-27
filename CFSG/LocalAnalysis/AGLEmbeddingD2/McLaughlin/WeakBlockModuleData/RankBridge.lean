module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.FixedPoint

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] {Γ W : Type*} [Group Γ] [AddCommGroup W] [MulAction Γ W]

theorem mem_centralizer_of_model_fixed {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1) (φ : L →* Γ)
    (ι : G → W) (hadd : ∀ a ∈ V, ∀ b ∈ V, ι (a * b) = ι a + ι b)
    (hker : ∀ v ∈ V, ι v = 0 ↔ v ∈ Subgroup.centralizer (L : Set G))
    (hequiv : ∀ l : L, ∀ v ∈ V, ι ((l : G) * v * (l : G)⁻¹) = φ l • ι v) {y : G} (hy : y ∈ V)
    (l : L) (hodd : Odd (orderOf (l : G))) (hfix : φ l • ι y = ι y) :
    (l : G) ∈ Subgroup.centralizer ({y} : Set G) := by
  have hlV : (l : G) * y * (l : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV l.2) y).mp hy
  have hcV : (l : G) * y * (l : G)⁻¹ * y⁻¹ ∈ V := V.mul_mem hlV (V.inv_mem hy)
  have hι : ι ((l : G) * y * (l : G)⁻¹ * y⁻¹) = 0 := by
    have h1 := hadd _ hcV y hy
    rw [inv_mul_cancel_right, hequiv l y hy, hfix] at h1
    exact add_eq_right.mp h1.symm
  exact mem_centralizer_of_comm_mem_centralizer hLV hV2 hy l.2 hodd ((hker _ hcV).mp hι)

theorem coprime_kernel_lifts_pSubgroup_map {Source Target : Type*} [Group Source] [Finite Source]
    [Group Target] (prime : ℕ) (hprime : prime.Prime) (f : Source →* Target)
    (hsurj : Function.Surjective f) (hkernel : prime.Coprime (Nat.card f.ker))
    (T : Subgroup Target) (hT : IsPGroup prime T) :
    ∃ lift : Subgroup Source, IsPGroup prime lift ∧ Subgroup.map f lift = T ∧
      Nonempty (lift ≃* T) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let pre := Subgroup.comap f T
  let rm : pre →* T := (f.comp pre.subtype).codRestrict T (fun element => element.property)
  have hrmSurj : Function.Surjective rm := by
    intro element
    obtain ⟨preimage, hpreimage⟩ := hsurj element.val
    have hmem : preimage ∈ pre := by
      change f preimage ∈ T
      rw [hpreimage]
      exact element.property
    exact ⟨⟨preimage, hmem⟩, Subtype.ext hpreimage⟩
  let targetSylow : Sylow prime T := Classical.choice inferInstance
  obtain ⟨sourceSylow, hsourceSylow⟩ := Sylow.mapSurjective_surjective hrmSurj prime targetSylow
  have htargetTop : (targetSylow : Subgroup T) = ⊤ :=
    top_le_iff.mp ((hT.to_subgroup (⊤ : Subgroup T)).le_sylow_of_normal targetSylow)
  have himageTop : Subgroup.map rm (sourceSylow : Subgroup pre) = ⊤ := by
    rw [← Sylow.coe_mapSurjective hrmSurj, hsourceSylow, htargetTop]
  let lift := Subgroup.map pre.subtype (sourceSylow : Subgroup pre)
  have hlift : IsPGroup prime lift := sourceSylow.isPGroup'.map pre.subtype
  have himage : Subgroup.map f lift = T := by
    have hmapped := congrArg (Subgroup.map T.subtype) himageTop
    rw [Subgroup.map_map, ← MonoidHom.range_eq_map, T.subtype_range] at hmapped
    have hmaps : T.subtype.comp rm = f.comp pre.subtype := by
      ext element
      rfl
    rw [hmaps, ← Subgroup.map_map] at hmapped
    exact hmapped
  obtain ⟨e⟩ := coprime_kernel_pGroup_equiv_image prime hprime f hkernel lift hlift
  exact ⟨lift, hlift, himage, ⟨e.trans (MulEquiv.subgroupCongr himage)⟩⟩

@[expose] def RankDropModel (Γ W : Type*) [Group Γ] [Finite Γ] [MulAction Γ W] : Prop :=
  ∀ w : W, ∃ (E : Subgroup Γ) (k : ℕ), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k ∧
    (∀ g ∈ E, g • w = w) ∧ pRank 3 (⊤ : Subgroup Γ) ≤ k + 1

theorem pRank_le_pRank_centralizer_add_one_of_model [Finite G] [Finite Γ] {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1) (φ : L →* Γ)
    (hφ : Function.Surjective φ) (hcop : Nat.Coprime 3 (Nat.card φ.ker)) (ι : G → W)
    (hadd : ∀ a ∈ V, ∀ b ∈ V, ι (a * b) = ι a + ι b)
    (hker : ∀ v ∈ V, ι v = 0 ↔ v ∈ Subgroup.centralizer (L : Set G))
    (hequiv : ∀ l : L, ∀ v ∈ V, ι ((l : G) * v * (l : G)⁻¹) = φ l • ι v)
    (hrd : RankDropModel Γ W) :
    ∀ y ∈ V, pRank 3 L ≤ pRank 3 (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) + 1 := by
  intro y hy
  obtain ⟨E, k, hE, hEcard, hEfix, hrank⟩ := hrd (ι y)
  obtain ⟨lift, hlift3, himage, ⟨e⟩⟩ := coprime_kernel_lifts_pSubgroup_map 3 Nat.prime_three φ hφ
    hcop E (elementary_isPGroup 3 E hE)
  have hlE : IsElemAbelian 3 lift := elementary_transport 3 E lift e.symm hE
  have hlcard : Nat.card lift = 3 ^ k := (Nat.card_congr e.toEquiv).trans hEcard
  set D : Subgroup G := Subgroup.map L.subtype lift with hD
  have hDle : D ≤ L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨l.2, ?_⟩
    have hodd : Odd (orderOf (l : G)) := by
      obtain ⟨j, hj⟩ := hlift3 ⟨l, hl⟩
      have h1 : (l : G) ^ (3 ^ j) = 1 := by
        have := congrArg (fun z : lift => ((z : L) : G)) hj
        simpa using this
      exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one h1)
    exact mem_centralizer_of_model_fixed hLV hV2 φ ι hadd hker hequiv hy l hodd
      (hEfix _ (himage ▸ Subgroup.mem_map_of_mem φ hl))
  have hDcard : Nat.card D = 3 ^ k := by
    rw [hD, Subgroup.card_map_of_injective L.subtype_injective, hlcard]
  have hDE : IsElemAbelian 3 D := elementary_map_injective 3 lift L.subtype L.subtype_injective hlE
  have h1 : k ≤ pRank 3 (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
    unfold pRank
    exact le_csSup (pRank_set_bddAbove 3 (by norm_num) _) ⟨D, hDle, hDE, hDcard⟩
  have h2 : pRank 3 L = pRank 3 (⊤ : Subgroup Γ) := by
    rw [pRank_subgroup_eq_internal_top 3 (by norm_num) L]
    exact pRank_top_eq_of_coprime_kernel 3 Nat.prime_three φ hφ hcop
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
