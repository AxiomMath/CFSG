module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

namespace PartC

variable {H H' G : Type} [Group H] [Group H'] [Group G] (f : H →* H') (g : H →* G)
  {T : Subgroup H} {Q' P' : Subgroup H'} {e u : H}

theorem transport (hf : ∀ a ∈ T, ∀ b ∈ T, f a = f b → a = b) (hg : Function.Injective g)
    (heT : e ∈ T) (huT : u ∈ T) (hc : PartC (T.map f) Q' P' (f e) (f u))
    (hge : g e ∈ Subgroup.center G) :
    PartC (T.map g) ((T ⊓ Q'.comap f).map g) ((T ⊓ P'.comap f).map g) (g e) (g u) := by
  set A := T ⊓ Q'.comap f with hA
  set B := T ⊓ P'.comap f with hB
  have hfT : ∀ {t : H}, t ∈ T → f t ∈ T.map f := fun ht => Subgroup.mem_map_of_mem f ht
  have hpre : ∀ {x : H'}, x ∈ T.map f → ∃ t ∈ T, f t = x := fun hx => Subgroup.mem_map.mp hx
  have hsup : ∀ {t : H}, t ∈ T → f t ∈ Q' ⊔ P' → g t ∈ A.map g ⊔ B.map g := by
    intro t ht h
    obtain ⟨q', hq', p', hp', hqp⟩ := hc.mem_sup_iff.mp h
    obtain ⟨a, haT, rfl⟩ := hpre (hc.left_le hq')
    obtain ⟨b, hbT, rfl⟩ := hpre (hc.right_le hp')
    have htab : t = a * b := hf _ ht _ (T.mul_mem haT hbT) (by rw [map_mul, hqp])
    rw [htab, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, ⟨haT, hq'⟩, rfl⟩)
      (Subgroup.mem_sup_right ⟨b, ⟨hbT, hp'⟩, rfl⟩)
  have hsup' : ∀ {t : H}, g t ∈ A.map g ⊔ B.map g → f t ∈ Q' ⊔ P' := by
    intro t h
    rw [← Subgroup.map_sup, Subgroup.mem_map_iff_mem hg] at h
    have hle : A ⊔ B ≤ (Q' ⊔ P').comap f :=
      _root_.sup_le (inf_le_right.trans (Subgroup.comap_mono le_sup_left))
        (inf_le_right.trans (Subgroup.comap_mono le_sup_right))
    exact hle h
  have hone : ∀ {t : H}, t ∈ T → f t = 1 → t = 1 := fun ht h =>
    hf _ ht _ T.one_mem (by rw [h, map_one])
  have hord : ∀ {t : H}, t ∈ T → orderOf t = 2 → orderOf (f t) = 2 := by
    intro t ht h2
    have htt : t ^ 2 = 1 := by rw [← h2, pow_orderOf_eq_one]
    refine orderOf_eq_prime (by rw [← map_pow, htt, map_one]) fun h => ?_
    rw [hone ht h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hord' : ∀ {t : H}, t ∈ T → orderOf (f t) = 2 → orderOf t = 2 := by
    intro t ht h2
    have htt : f (t ^ 2) = f 1 := by rw [map_pow, ← h2, pow_orderOf_eq_one, map_one]
    refine orderOf_eq_prime (hf _ (T.pow_mem ht 2) _ T.one_mem htt) fun h => ?_
    rw [h, map_one, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hordg : ∀ t : H, orderOf (g t) = orderOf t := fun t => orderOf_injective g hg t
  have hT2 : IsPGroup 2 T := by
    rintro ⟨t, ht⟩
    obtain ⟨n, hn⟩ := hc.isPGroup ⟨f t, hfT ht⟩
    refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    refine hf _ (T.pow_mem ht _) _ T.one_mem ?_
    rw [map_pow, map_one]
    simpa using congrArg Subtype.val hn
  let ψ : A →* Q' := (f.comp A.subtype).codRestrict Q' fun a => a.2.2
  have hψ : Function.Bijective ψ := by
    refine ⟨fun a b hab => Subtype.ext (hf _ a.2.1 _ b.2.1 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨q', hq'⟩
    obtain ⟨a, haT, rfl⟩ := hpre (hc.left_le hq')
    exact ⟨⟨a, haT, hq'⟩, rfl⟩
  obtain ⟨φ⟩ := hc.quaternion
  exact
    { isPGroup := hT2.map g
      left_le := Subgroup.map_mono inf_le_left
      right_le := Subgroup.map_mono inf_le_left
      quaternion := ⟨((A.equivMapOfInjective g hg).symm.trans (MulEquiv.ofBijective ψ hψ)).trans φ⟩
      commute := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact hf _ (T.mul_mem ha.1 hb.1) _ (T.mul_mem hb.1 ha.1)
          (by rw [map_mul, map_mul, hc.commute _ ha.2 _ hb.2])
      mem_inf := by
        rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
        obtain rfl := hg hab
        rcases hc.mem_inf _ ha.2 hb.2 with h | h
        · exact Or.inl (by rw [hone ha.1 h, map_one])
        · exact Or.inr (by rw [hf _ ha.1 _ heT h])
      order := by rw [hordg, hord' heT hc.order]
      center := hge
      mem_left := ⟨e, ⟨heT, hc.mem_left⟩, rfl⟩
      mem_right := ⟨e, ⟨heT, hc.mem_right⟩, rfl⟩
      self_mem := ⟨u, ⟨huT, hc.self_mem⟩, rfl⟩
      sq := by
        rw [← map_mul, hf _ (T.mul_mem huT huT) _ heT (by rw [map_mul, hc.sq])]
      unique := by
        rintro _ ⟨b, hb, rfl⟩ h2
        rw [hordg] at h2
        rw [hf _ hb.1 _ heT (hc.unique _ hb.2 (hord hb.1 h2))]
      normal_left := by
        rintro _ ⟨t, ht, rfl⟩ _ ⟨a, ha, rfl⟩
        refine ⟨t * a * t⁻¹, ⟨T.mul_mem (T.mul_mem ht ha.1) (T.inv_mem ht), ?_⟩, by simp⟩
        change f (t * a * t⁻¹) ∈ Q'
        rw [map_mul, map_mul, map_inv]
        exact hc.normal_left _ (hfT ht) _ ha.2
      normal_right := by
        rintro _ ⟨t, ht, rfl⟩ _ ⟨b, hb, rfl⟩
        refine ⟨t * b * t⁻¹, ⟨T.mul_mem (T.mul_mem ht hb.1) (T.inv_mem ht), ?_⟩, by simp⟩
        change f (t * b * t⁻¹) ∈ P'
        rw [map_mul, map_mul, map_inv]
        exact hc.normal_right _ (hfT ht) _ hb.2
      involution_mem := by
        rintro _ ⟨t, ht, rfl⟩ h2
        rw [hordg] at h2
        exact hsup ht (hc.involution_mem _ (hfT ht) (hord ht h2))
      inv_mul_mem := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ha' hb'
        rw [← map_inv, ← map_mul]
        refine hsup (T.mul_mem (T.inv_mem ha) hb) ?_
        rw [map_mul, map_inv]
        exact hc.inv_mul_mem _ (hfT ha) _ (hfT hb) (fun h => ha' (hsup ha h))
          (fun h => hb' (hsup hb h))
      outer := by
        rintro _ ⟨y, hy, rfl⟩ hy'
        obtain ⟨m', hm', hm1, hm2⟩ := hc.outer _ (hfT hy) (fun h => hy' (hsup hy h))
        obtain ⟨m, hmT, rfl⟩ := hpre (hc.left_le hm')
        refine ⟨g m, ⟨m, ⟨hmT, hm'⟩, rfl⟩, fun h => hm1 ?_, fun h => hm2 ?_⟩
        · rw [← map_inv, ← map_mul, ← map_mul] at h ⊢
          rw [hg h]
        · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul] at h
          rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, hg h] }

end PartC

variable {J : Type} [Group J] [Finite J] {u : J}

abbrev partCSylow (T : Sylow 2 (quasiNormalizer u)) : Subgroup J :=
  (T : Subgroup (quasiNormalizer u)).map (quasiNormalizer u).subtype

abbrev partCLeft (T : Sylow 2 (quasiNormalizer u)) (L : Subgroup (QuasiQuotient u)) :
    Subgroup J :=
  ((T : Subgroup (quasiNormalizer u)) ⊓ L.comap (quasiMk u)).map (quasiNormalizer u).subtype

abbrev partCRight (T : Sylow 2 (quasiNormalizer u)) (L : Subgroup (QuasiQuotient u)) :
    Subgroup J :=
  ((T : Subgroup (quasiNormalizer u)) ⊓
    (Subgroup.centralizer (L : Set (QuasiQuotient u))).comap (quasiMk u)).map
      (quasiNormalizer u).subtype

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
