module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Alt
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4NXCoord
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Hexa

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_map_mk'_mul_card {N H V : Subgroup G} [(H.subgroupOf N).Normal] (hHV : H ≤ V)
    (hVN : V ≤ N) :
    Nat.card ((V.subgroupOf N).map (QuotientGroup.mk' (H.subgroupOf N))) * Nat.card H =
      Nat.card V := by
  have h := Subgroup.card_ker_mul_card_range
    ((QuotientGroup.mk' (H.subgroupOf N)).comp (V.subgroupOf N).subtype)
  rw [MonoidHom.range_comp, range_subtype, ← MonoidHom.comap_ker, QuotientGroup.ker_mk'] at h
  have h1 : Nat.card ((H.subgroupOf N).comap (V.subgroupOf N).subtype) = Nat.card H := by
    have hle : H.subgroupOf N ≤ V.subgroupOf N := subgroupOf_mono N hHV
    calc Nat.card ((H.subgroupOf N).comap (V.subgroupOf N).subtype)
        = Nat.card (H.subgroupOf N) := Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
      _ = Nat.card H := Nat.card_congr (subgroupOfEquivOfLe (hHV.trans hVN)).toEquiv
  have h2 : Nat.card (V.subgroupOf N) = Nat.card V :=
    Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv
  rw [h1, h2, mul_comm] at h
  exact h

structure Sec2HexaCoord (E A F : Subgroup G) (rep : Fin 64 → G) (e : ↥(sec2PlanesP E F) ≃ Fin 6)
    (ψ : ↥(normalizer (sec2P E : Set G)) →* Equiv.Perm (Fin 64)) : Prop where
  mem : ∀ v, rep v ∈ sec2P E
  surj : ∀ p ∈ sec2P E, ∃ v, p⁻¹ * rep v ∈ E ⊓ A
  inj : ∀ v w, (rep v)⁻¹ * rep w ∈ E ⊓ A → v = w
  add : ∀ v w, (rep (xorF v w))⁻¹ * (rep v * rep w) ∈ E ⊓ A
  plane : ∀ (V : ↥(sec2PlanesP E F)) (v : Fin 64),
    rep v ∈ (V : Subgroup G) ↔ v.val ∈ hexaOval[(e V : ℕ)]!
  conj : ∀ n v, (rep (ψ n v))⁻¹ * ((n : G) * rep v * (n : G)⁻¹) ∈ E ⊓ A
  psi_add : ∀ n v w, ψ n (xorF v w) = xorF (ψ n v) (ψ n w)

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
  (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))

include h11 hE16 hF hL hodd hx hxS h4

omit h11 hE16 hL hodd hx hxS h4 in
theorem inf_le_normalizer_sec2P : E ⊓ A ≤ normalizer (sec2P E : Set G) :=
  (inf_le_left.trans (le_sec2P_of_frame hF)).trans le_normalizer

theorem normal_inf_subgroupOf :
    ((E ⊓ A).subgroupOf (normalizer (sec2P E : Set G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer (inf_le_normalizer_sec2P hF)).mpr
    (normalizer_sec2P_le_normalizer_inf h11 hE16 hF hL hodd hx hxS h4)

theorem exists_sec2HexaCoord :
    ∃ (rep : Fin 64 → G) (e : ↥(sec2PlanesP E F) ≃ Fin 6)
      (ψ : ↥(normalizer (sec2P E : Set G)) →* Equiv.Perm (Fin 64)),
      Sec2HexaCoord E A F rep e ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (sec2P E : Set G) with hN
  set H := (E ⊓ A).subgroupOf N with hH
  have : H.Normal := normal_inf_subgroupOf h11 hE16 hF hL hodd hx hxS h4
  set π := QuotientGroup.mk' H with hπ
  have hπeq : ∀ a b : ↥N, π a = π b ↔ ((a : G)⁻¹ * b) ∈ E ⊓ A := fun a b => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hH,
      mem_subgroupOf]
    simp
  have hPN : sec2P E ≤ N := le_normalizer
  have hEAP : E ⊓ A ≤ sec2P E := inf_le_left.trans (le_sec2P_of_frame hF)
  have hsq := fun {a b : G} (ha : a ∈ sec2P E) (hb : b ∈ sec2P E) =>
    sq_mem_and_commutator_mem_inf h11 hE16 hF hL hodd hx hxS h4 ha hb
  set ι : Subgroup G → Subgroup (↥N ⧸ H) := fun V => (V.subgroupOf N).map π with hι
  have hmemι : ∀ {V : Subgroup G} {q : ↥N ⧸ H}, q ∈ ι V ↔ ∃ v : ↥N, (v : G) ∈ V ∧ π v = q := by
    intro V q
    simp only [hι, mem_map, mem_subgroupOf]
  have hEAV : ∀ V ∈ sec2PlanesP E F, E ⊓ A ≤ V := fun V hV =>
    inf_le_of_mem_planes_of_le h11 hE16 hF hL hodd hV.1 hV.2
  have hback : ∀ {V : Subgroup G}, E ⊓ A ≤ V → ∀ p : ↥N, π p ∈ ι V → (p : G) ∈ V := by
    intro V hEV p hp
    obtain ⟨u, hu, hup⟩ := hmemι.mp hp
    have h := (hπeq u p).mp hup
    have : (p : G) = u * ((u : G)⁻¹ * p) := by group
    rw [this]
    exact mul_mem hu (hEV h)
  have hcomm : ∀ a ∈ ι (sec2P E), ∀ b ∈ ι (sec2P E), a * b = b * a := by
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := hmemι.mp ha
    obtain ⟨q, hq, rfl⟩ := hmemι.mp hb
    rw [← map_mul, ← map_mul, hπeq]
    have := (hsq (inv_mem hq) (inv_mem hp)).2
    simpa [mul_assoc] using this
  have hsq' : ∀ a ∈ ι (sec2P E), a * a = 1 := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := hmemι.mp ha
    rw [← map_mul, ← map_one π, hπeq]
    have := (hsq hp hp).1
    simpa using inv_mem this
  have hcard : ∀ {V : Subgroup G}, E ⊓ A ≤ V → V ≤ sec2P E →
      Nat.card (ι V) * 16 = Nat.card V := fun hEV hVP => by
    have h := card_map_mk'_mul_card (H := E ⊓ A) hEV (hVP.trans hPN)
    rwa [card_inf_left hF hodd] at h
  have h64 : Nat.card (ι (sec2P E)) = 64 := by
    have h := hcard hEAP le_rfl
    rw [card_sec2P_of_frame h11 hE16 hF hL hodd] at h
    omega
  have hle : ∀ W ∈ ι '' sec2PlanesP E F, W ≤ ι (sec2P E) := by
    rintro _ ⟨V, hV, rfl⟩
    exact map_mono (subgroupOf_mono N hV.2)
  have h4' : ∀ W ∈ ι '' sec2PlanesP E F, Nat.card W = 4 := by
    rintro _ ⟨V, hV, rfl⟩
    have h := hcard (hEAV V hV) hV.2
    rw [(isElemAbelian_and_card_of_mem_planes hF hV.1).2] at h
    omega
  have hinj : Set.InjOn ι (sec2PlanesP E F) := by
    intro V hV V' hV' h
    refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
    · have := hback (hEAV V' hV') ⟨v, hV.2.trans hPN hv⟩ (h ▸ hmemι.mpr ⟨_, hv, rfl⟩)
      exact this
    · have := hback (hEAV V hV) ⟨v, hV'.2.trans hPN hv⟩ (h.symm ▸ hmemι.mpr ⟨_, hv, rfl⟩)
      exact this
  have h6 : Nat.card (ι '' sec2PlanesP E F) = 6 := by
    rw [Nat.card_image_of_injOn hinj]
    exact ncard_planes_sec2P h11 hE16 hF hL hodd hx hxS h4
  have hgp : ∀ W₁ ∈ ι '' sec2PlanesP E F, ∀ W₂ ∈ ι '' sec2PlanesP E F,
      ∀ W₃ ∈ ι '' sec2PlanesP E F, W₁ ≠ W₂ → W₁ ≠ W₃ → W₂ ≠ W₃ → W₃ ⊓ (W₁ ⊔ W₂) = ⊥ := by
    rintro _ ⟨V₁, hV₁, rfl⟩ _ ⟨V₂, hV₂, rfl⟩ _ ⟨V₃, hV₃, rfl⟩ h12 h13 h23
    have hgen := inf_sup_eq_of_mem_planes h11 hE16 hF hL hodd hx hxS h4 hV₁.1 hV₁.2 hV₂.1
      hV₂.2 hV₃.1 hV₃.2 (fun h => h12 (h ▸ rfl)) (fun h => h13 (h ▸ rfl)) (fun h => h23 (h ▸ rfl))
    rw [eq_bot_iff]
    rintro q ⟨hq₃, hq₁₂⟩
    have hsup : ι V₁ ⊔ ι V₂ = ((V₁ ⊔ V₂).subgroupOf N).map π := by
      rw [hι, ← Subgroup.map_sup, subgroupOf_sup (hV₁.2.trans hPN) (hV₂.2.trans hPN)]
    rw [hsup] at hq₁₂
    obtain ⟨u, hu, rfl⟩ := hq₁₂
    have hu₃ : (u : G) ∈ V₃ := hback (hEAV V₃ hV₃) u hq₃
    have hmem : (u : G) ∈ V₃ ⊓ (V₁ ⊔ V₂) := ⟨hu₃, hu⟩
    rw [hgen] at hmem
    rw [mem_bot, ← map_one π, hπeq]
    simpa using inv_mem hmem
  have hEpl : E ∈ sec2PlanesP E F :=
    ⟨⟨1, Or.inl (rightConjugate_one E).symm⟩, le_sec2P_of_frame hF⟩
  obtain ⟨repQ, hc⟩ := exists_hexaCoord Hexa.hexaStab_check hcomm hsq' h64 hle h4' hgp h6
    (Set.mem_image_of_mem ι hEpl)
  have hlift : ∀ v, ∃ p : ↥N, (p : G) ∈ sec2P E ∧ π p = repQ v := fun v => hmemι.mp (hc.mem v)
  choose lift hliftP hliftπ using hlift
  have hlab : ∀ V : ↥(sec2PlanesP E F), ∃ j : Fin 6, ∀ v,
      repQ v ∈ ι (V : Subgroup G) ↔ v.val ∈ hexaOval[(j : ℕ)]! := by
    intro V
    obtain ⟨j, hj, hjV⟩ := hc.pt _ (Set.mem_image_of_mem ι V.2)
    exact ⟨⟨j, hj⟩, hjV⟩
  choose lab hlabV using hlab
  have hlabinj : Function.Injective lab := by
    intro V V' h
    have hι' : ι (V : Subgroup G) = ι (V' : Subgroup G) := by
      ext q
      refine ⟨fun hq => ?_, fun hq => ?_⟩
      · obtain ⟨v, rfl⟩ := hc.surj q (hle _ (Set.mem_image_of_mem ι V.2) hq)
        rw [hlabV, ← h, ← hlabV]
        exact hq
      · obtain ⟨v, rfl⟩ := hc.surj q (hle _ (Set.mem_image_of_mem ι V'.2) hq)
        rw [hlabV, h, ← hlabV]
        exact hq
    exact Subtype.ext (hinj V.2 V'.2 hι')
  have hlabbij : Function.Bijective lab := hlabinj.bijective_of_nat_card_le (by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact (ncard_planes_sec2P h11 hE16 hF hL hodd hx hxS h4).ge)
  have hXn : (ι (sec2P E)).Normal := by
    have h1 : ((sec2P E).subgroupOf N).Normal :=
      (normal_subgroupOf_iff_le_normalizer hPN).mpr le_rfl
    exact h1.map π (QuotientGroup.mk'_surjective H)
  set eX : Fin 64 ≃ ↥(ι (sec2P E)) := Equiv.ofBijective (fun v => ⟨repQ v, hc.mem v⟩)
    ⟨fun v w h => hc.inj (congrArg Subtype.val h), fun q => by
      obtain ⟨v, hv⟩ := hc.surj q.1 q.2
      exact ⟨v, Subtype.ext hv⟩⟩ with heX
  set ψ : ↥N →* Equiv.Perm (Fin 64) := (Equiv.permCongrHom eX.symm).toMonoidHom.comp
    ((MulAut.toPerm ↥(ι (sec2P E))).comp ((MulAut.conjNormal (H := ι (sec2P E))).comp π))
    with hψ
  have hrepψ : ∀ n v, repQ (ψ n v) = π n * repQ v * (π n)⁻¹ := by
    intro n v
    have h : (eX (ψ n v) : ↥N ⧸ H) = π n * repQ v * (π n)⁻¹ := by
      simp only [hψ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
      exact MulAut.conjNormal_apply (π n) (eX v)
    exact h
  refine ⟨fun v => (lift v : G), Equiv.ofBijective lab hlabbij, ψ, ⟨hliftP, ?_, ?_, ?_, ?_, ?_,
    ?_⟩⟩
  · intro p hp
    obtain ⟨v, hv⟩ := hc.surj (π ⟨p, hPN hp⟩) (hmemι.mpr ⟨_, hp, rfl⟩)
    refine ⟨v, ?_⟩
    have h := (hπeq ⟨p, hPN hp⟩ (lift v)).mp (by rw [hliftπ, hv])
    exact h
  · intro v w h
    exact hc.inj (by rw [← hliftπ, ← hliftπ]; exact (hπeq _ _).mpr h)
  · intro v w
    have h : π (lift (xorF v w)) = π (lift v * lift w) := by
      rw [map_mul, hliftπ, hliftπ, hliftπ, hc.add]
    simpa using (hπeq _ _).mp h
  · intro V v
    rw [Equiv.ofBijective_apply, ← hlabV]
    constructor
    · intro h
      exact hmemι.mpr ⟨lift v, h, hliftπ v⟩
    · intro h
      rw [← hliftπ] at h
      exact hback (hEAV V V.2) (lift v) h
  · intro n v
    have h : π (lift (ψ n v)) = π (n * lift v * n⁻¹) := by
      rw [hliftπ, hrepψ, map_mul, map_mul, map_inv, hliftπ]
    simpa using (hπeq _ _).mp h
  · intro n v w
    apply hc.inj
    rw [hrepψ, hc.add, hc.add, hrepψ, hrepψ]
    group

end Frame

end CFSG.ComponentClassification.AS81
