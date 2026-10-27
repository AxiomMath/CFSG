module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDQ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

namespace HeDL

variable {H : Type} [Group H] [Finite H]

theorem exists_sylow_lift {W : Subgroup H} {E : Subgroup (H ⧸ pPrimeCore 2 H)} (hE : IsElemTwo E)
    (hWE : W.map (QuotientGroup.mk' (pPrimeCore 2 H)) = E) :
    ∃ Z : Subgroup H, Z ≤ W ∧ Z.map (QuotientGroup.mk' (pPrimeCore 2 H)) = E ∧ IsElemTwo Z ∧
      Nat.card Z = Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥W) := inferInstance
  have hWE' : ∀ w : ↥W, π w ∈ E := fun w => hWE ▸ mem_map_of_mem π w.2
  let f : ↥W →* ↥E := (π.comp W.subtype).codRestrict E hWE'
  have hf : Function.Surjective f := by
    rintro ⟨e, he⟩
    rw [← hWE] at he
    obtain ⟨w, hw, rfl⟩ := he
    exact ⟨⟨w, hw⟩, rfl⟩
  have htop : ((S.mapSurjective hf : Sylow 2 ↥E) : Subgroup ↥E) = ⊤ :=
    ((S.mapSurjective hf).is_maximal' (hE.isPGroup.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  set Z := (S : Subgroup ↥W).map W.subtype with hZ
  have hZp : IsPGroup 2 Z := S.isPGroup'.map W.subtype
  have hinj := GSThmB.OddQuot.injOn_of_isPGroup hZp
  have hZE : Z.map π = E := by
    ext e
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, -, rfl⟩ := hz
      exact hWE' w
    · intro he
      have hmem : (⟨e, he⟩ : ↥E) ∈ (S : Subgroup ↥W).map f := by rw [htop]; exact mem_top _
      obtain ⟨w, hw, hwe⟩ := hmem
      exact ⟨(w : H), ⟨w, hw, rfl⟩, congrArg Subtype.val hwe⟩
  have hZE' : ∀ x ∈ Z, π x ∈ E := fun x hx => hZE ▸ mem_map_of_mem π hx
  refine ⟨Z, map_subtype_le _, hZE, ⟨fun x hx y hy => ?_, fun x hx => ?_⟩, ?_⟩
  · exact hinj (mul_mem hx hy) (mul_mem hy hx) (by
      rw [map_mul, map_mul]
      exact hE.1 _ (hZE' x hx) _ (hZE' y hy))
  · exact hinj (mul_mem hx hx) (one_mem _) (by
      rw [map_mul, map_one]
      exact hE.2 _ (hZE' x hx))
  · rw [← hZE, GSThmB.OddQuot.card_map_of_isPGroup hZp]

theorem exists_lift_le {R : Subgroup H} {E : Subgroup (H ⧸ pPrimeCore 2 H)} (hE : IsElemTwo E)
    (hER : E ≤ R.map (QuotientGroup.mk' (pPrimeCore 2 H))) :
    ∃ Z : Subgroup H, Z ≤ R ∧ Z.map (QuotientGroup.mk' (pPrimeCore 2 H)) = E ∧ IsElemTwo Z ∧
      Nat.card Z = Nat.card E := by
  obtain ⟨Z, hZW, hZ⟩ := exists_sylow_lift hE (GSThmB.OddQuot.map_inf_comap_eq hER)
  exact ⟨Z, hZW.trans inf_le_left, hZ⟩

theorem exists_lift_centralizing {R : Subgroup H} (hR : IsPGroup 2 R)
    {E : Subgroup (H ⧸ pPrimeCore 2 H)} (hE : IsElemTwo E)
    (hRE : ∀ r ∈ R, ∀ e ∈ E, QuotientGroup.mk' (pPrimeCore 2 H) r * e =
      e * QuotientGroup.mk' (pPrimeCore 2 H) r) :
    ∃ Z : Subgroup H, Z ≤ centralizer (R : Set H) ∧
      Z.map (QuotientGroup.mk' (pPrimeCore 2 H)) = E ∧ IsElemTwo Z ∧
      Nat.card Z = Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set Y : Subgroup H := E.comap π with hY
  have hRY : R ≤ normalizer (Y : Set H) := by
    intro r hr
    rw [mem_normalizer_iff]
    intro y
    simp only [hY, mem_comap, map_mul, map_inv]
    constructor
    · intro h
      rw [hRE r hr _ h, mul_inv_cancel_right]
      exact h
    · intro h
      have h3 := hRE r hr _ h
      have h4 : π y = (π r)⁻¹ * (π r * π y * (π r)⁻¹) * π r := by group
      rw [h4, mul_assoc, ← h3, ← mul_assoc, inv_mul_cancel, one_mul]
      exact h
  have hker : ¬ 2 ∣ Nat.card (π.domRestrict Y).ker :=
    GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict π GSThmB.OddQuot.not_two_dvd_card_ker Y
  have hmap := GSThmB.OddQuot.map_inf_centralizer π hR hRY hker
  have hYE : Y.map π = E := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) E
  have hEC : E ≤ centralizer ((R.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) := by
    intro e he
    rw [mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    exact hRE r hr e he
  rw [hYE, inf_of_le_left hEC] at hmap
  obtain ⟨Z, hZW, hZ⟩ := exists_sylow_lift hE hmap
  exact ⟨Z, hZW.trans inf_le_right, hZ⟩

theorem normalizes_of_central {M : Subgroup H} (hM : IsPComponent 2 M) {z : H}
    (hz : ∀ m ∈ M, QuotientGroup.mk' (pPrimeCore 2 H) z * QuotientGroup.mk' (pPrimeCore 2 H) m =
      QuotientGroup.mk' (pPrimeCore 2 H) m * QuotientGroup.mk' (pPrimeCore 2 H) z) :
    z ∈ normalizer (M : Set H) ∧
      ∀ m ∈ M, z * m * z⁻¹ * m⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set Mz := M.map (MulAut.conj z).toMonoidHom with hMz
  have hMzp : IsPComponent 2 Mz :=
    ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
      (MulAut.conj z)).1 M).mp hM
  have hconj : ∀ m ∈ M, π (z * m * z⁻¹) = π m := fun m hm => by
    rw [map_mul, map_mul, map_inv, hz m hm, mul_inv_cancel_right]
  have hmapeq : Mz.map π = M.map π := by
    ext q
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨m, hm, (hconj m hm).symm⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨z * m * z⁻¹, ⟨m, hm, rfl⟩, hconj m hm⟩
  have heq : Mz = M := GSThmB.OddQuot.eq_of_map_eq π GSThmB.OddQuot.not_two_dvd_card_ker
    (X := ⊤) le_top le_top
    (CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hMzp le_top)
    (CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hM le_top) hmapeq
  have hN : z ∈ normalizer (M : Set H) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← heq]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← heq] at hy
      obtain ⟨m, hm, hmy⟩ := hy
      have : m = y := by
        have h := congrArg (fun w => z⁻¹ * w * z) hmy
        simpa [mul_assoc] using h
      rw [← this]
      exact hm
  refine ⟨hN, fun m hm => ?_⟩
  have h1 : z * m * z⁻¹ * m⁻¹ ∈ M :=
    mul_mem ((mem_normalizer_iff.mp hN m).mp hm) (inv_mem hm)
  have h2 : z * m * z⁻¹ * m⁻¹ ∈ pPrimeCore 2 H := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 H), MonoidHom.mem_ker, map_mul, hconj m hm,
      map_inv, mul_inv_cancel]
  exact GSThmB.OddQuot.inf_pPrimeCore_le_oddCoreIn M (mem_inf.mpr ⟨h1, h2⟩)

end HeDL

end CFSG.ComponentClassification.GrSLit
