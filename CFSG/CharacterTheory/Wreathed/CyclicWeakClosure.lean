module

public import CFSG.CharacterTheory.Semidihedral.OddCoreQuotient
public import CFSG.Adapters.Involutions
public import CFSG.GroupTheory.NormalizerSylow
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalizerComplement

public noncomputable section

namespace CFSG.Wreathed

open scoped Pointwise

universe u v

theorem weakClosure_oddCore_eq_pPrimeCore (G : Type u) [Group G] :
    CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  apply le_antisymm
  · exact sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  · exact sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mp hN.2⟩

theorem oddCore_quotient_eq_bot_of_central_two
    {G : Type u} [Group G] [Finite G] (A : Subgroup G)
    (hA : A ≤ Subgroup.center G) (hAtwo : IsPGroup 2 A)
    (hcore : CFSG.oddCore G = ⊥) :
    let : A.Normal := Subgroup.normal_of_le_center hA
    CFSG.oddCore (G ⧸ A) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : A.Normal := Subgroup.normal_of_le_center hA
  change CFSG.oddCore (G ⧸ A) = ⊥
  rw [weakClosure_oddCore_eq_pPrimeCore] at hcore ⊢
  exact CFSG.Semidihedral.OddCoreQuotient.pPrimeCore_quotient_eq_bot_of_central
    2 A hA hAtwo hcore

theorem pSubgroup_conjugate_into_sylow_by_normal
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (R P : Subgroup G) [R.Normal]
    (hP : IsPGroup p P) (hPRS : P ≤ R ⊔ (S : Subgroup G)) :
    ∃ r ∈ R, ∀ x ∈ P, r⁻¹ * x * r ∈ (S : Subgroup G) := by
  let J : Subgroup G := R ⊔ (S : Subgroup G)
  let T : Sylow p J := S.subtype (show (S : Subgroup G) ≤ J from le_sup_right)
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := J)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq J Q T
  have hcJ : (c : G) ∈ (S : Subgroup G) ⊔ R := by
    simpa only [J, sup_comm] using c.property
  obtain ⟨s, hs, r, hr, hsr⟩ := Subgroup.mem_sup_of_normal_right.mp hcJ
  refine ⟨r⁻¹, R.inv_mem hr, ?_⟩
  intro x hx
  let xJ : J := ⟨x, hPRS hx⟩
  have hxQ : xJ ∈ (Q : Subgroup J) := hQ hx
  have hcx : MulAut.conj c xJ ∈ ((c • Q : Sylow p J) : Subgroup J) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hxQ
  rw [hc, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hcx
  have hcx' : (s * r) * x * (s * r)⁻¹ ∈ (S : Subgroup G) := by
    simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, xJ,
      ← hsr] using hcx
  have hremove := (S : Subgroup G).mul_mem
    ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs) hcx') hs
  convert hremove using 1
  group

theorem weakClosure_map_quotient
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (R A : Subgroup G) [R.Normal]
    (hAS : A ≤ (S : Subgroup G))
    (hwc : ∀ a ∈ A, ∀ g : G,
      g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g = a) :
    let q := QuotientGroup.mk' R
    let T := S.mapSurjective (QuotientGroup.mk'_surjective R)
    ∀ a ∈ A.map q, ∀ g : G ⧸ R,
      g⁻¹ * a * g ∈ (T : Subgroup (G ⧸ R)) → g⁻¹ * a * g = a := by
  let q := QuotientGroup.mk' R
  let T := S.mapSurjective (QuotientGroup.mk'_surjective R)
  change ∀ a ∈ A.map q, ∀ g : G ⧸ R,
    g⁻¹ * a * g ∈ (T : Subgroup (G ⧸ R)) → g⁻¹ * a * g = a
  rintro a ⟨b, hb, rfl⟩ g hg
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective R g
  have hmap : q (h⁻¹ * b * h) ∈ (S : Subgroup G).map q := by
    simpa only [q, T, map_mul, map_inv, Sylow.coe_mapSurjective] using hg
  have hpre : h⁻¹ * b * h ∈ R ⊔ (S : Subgroup G) := by
    have hmem : h⁻¹ * b * h ∈ ((S : Subgroup G).map q).comap q := hmap
    simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk', sup_comm] using hmem
  have hP : IsPGroup p (Subgroup.zpowers (h⁻¹ * b * h)) := by
    have hz := (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hAS hb))).map
      (MulAut.conj h⁻¹).toMonoidHom
    rw [MonoidHom.map_zpowers] at hz
    change IsPGroup p (Subgroup.zpowers (h⁻¹ * b * (h⁻¹)⁻¹)) at hz
    rw [inv_inv] at hz
    exact hz
  obtain ⟨r, hr, hcon⟩ := pSubgroup_conjugate_into_sylow_by_normal S R
    (Subgroup.zpowers (h⁻¹ * b * h)) hP (Subgroup.zpowers_le.mpr hpre)
  have hmem : (h * r)⁻¹ * b * (h * r) ∈ (S : Subgroup G) := by
    have ht := hcon (h⁻¹ * b * h) (Subgroup.mem_zpowers _)
    simpa only [mul_inv_rev, mul_assoc] using ht
  have heq := congrArg q (hwc b hb (h * r) hmem)
  have hqr : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  simpa only [map_mul, map_inv, hqr, mul_one] using heq

theorem weakClosure_oddCore_card (G : Type u) [Group G] [Finite G] :
    Odd (Nat.card (CFSG.oddCore G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [weakClosure_oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem weakClosure_oddCore_quotient_eq_bot (G : Type u) [Group G] [Finite G] :
    CFSG.oddCore (G ⧸ CFSG.oddCore G) = ⊥ := by
  let R := CFSG.oddCore G
  let q := QuotientGroup.mk' R
  let B := CFSG.oddCore (G ⧸ R)
  let D := B.comap q
  have hcard : Nat.card R * Nat.card B = Nat.card D := by
    have h := (R.subgroupOf D).card_mul_index
    simpa only [R, D, B, q,
      CFSG.Semidihedral.OddCoreQuotient.quotient_preimage_kernel_card,
      CFSG.Semidihedral.OddCoreQuotient.quotient_preimage_kernel_index] using h
  have hodd : Odd (Nat.card D) := by
    rw [← hcard]
    exact (weakClosure_oddCore_card G).mul (weakClosure_oddCore_card (G ⧸ R))
  have hDR : D ≤ R := le_sSup ⟨inferInstance, hodd⟩
  have hmap : D.map q = B := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective R) B
  change B = ⊥
  apply le_antisymm _ bot_le
  rw [← hmap]
  rintro x ⟨y, hy, rfl⟩
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr (hDR hy))

theorem normal_cyclic_two_subgroup_central_of_sylow
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (B : Subgroup G) [B.Normal] [IsCyclic B]
    (hBS : B ≤ (S : Subgroup G))
    (hBC : B ≤ Subgroup.centralizer (S : Set G)) :
    B ≤ Subgroup.center G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAut := CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup
    B (S.isPGroup'.to_le hBS)
  have htrivial : ∀ g : G, MulAut.conjNormal (H := B) g = 1 := by
    apply CFSG.GorensteinWalter.hom_to_pGroup_eq_one_of_sylow hAut _ S
    intro s
    ext b
    change (s : G) * (b : G) * (s : G)⁻¹ = (b : G)
    have hcomm := Subgroup.mem_centralizer_iff.mp (hBC b.property) s s.property
    calc
      (s : G) * (b : G) * (s : G)⁻¹ = (b : G) * (s : G) * (s : G)⁻¹ := by rw [hcomm]
      _ = b := by group
  intro b hb
  rw [Subgroup.mem_center_iff]
  intro g
  have heq := congrArg (fun a : MulAut B => (a ⟨b, hb⟩ : G)) (htrivial g)
  change g * b * g⁻¹ = b at heq
  calc
    g * b = (g * b * g⁻¹) * g := by group
    _ = b * g := by rw [heq]

theorem weakClosure_map_centralizes
    {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (A S : Subgroup G)
    (hAC : A ≤ Subgroup.centralizer (S : Set G)) :
    A.map f ≤ Subgroup.centralizer (S.map f : Set H) := by
  rintro a ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro b ⟨y, hy, rfl⟩
  exact (map_mul f y x).symm.trans
    ((congrArg f (Subgroup.mem_centralizer_iff.mp (hAC hx) y hy)).trans
      (map_mul f x y))

theorem cyclic_weakClosure_central_of_oddCore_eq_bot
    {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (A : Subgroup G) [IsCyclic A]
    (hAS : A ≤ (S : Subgroup G))
    (hAC : A ≤ Subgroup.centralizer (S : Set G))
    (hwc : ∀ a ∈ A, ∀ g : G,
      g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g = a)
    (hcore : CFSG.oddCore G = ⊥) : A ≤ Subgroup.center G := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  let C : Subgroup G := A ⊓ Subgroup.center G
  have hCcentral : C ≤ Subgroup.center G := inf_le_right
  let : C.Normal := Subgroup.normal_of_le_center hCcentral
  let q := QuotientGroup.mk' C
  let T := S.mapSurjective (QuotientGroup.mk'_surjective C)
  let D : Subgroup (G ⧸ C) := A.map q
  have hCtwo : IsPGroup 2 C := (S.isPGroup'.to_le hAS).to_inf_left
  have hQcore : CFSG.oddCore (G ⧸ C) = ⊥ :=
    oddCore_quotient_eq_bot_of_central_two C hCcentral hCtwo hcore
  have hDT : D ≤ (T : Subgroup (G ⧸ C)) := by
    simpa only [T, Sylow.coe_mapSurjective] using (Subgroup.map_mono (f := q) hAS)
  have hDC : D ≤ Subgroup.centralizer (T : Set (G ⧸ C)) := by
    change D ≤ Subgroup.centralizer ((T : Subgroup (G ⧸ C)) : Set (G ⧸ C))
    rw [show (T : Subgroup (G ⧸ C)) = (S : Subgroup G).map q from
      Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective C) S]
    exact weakClosure_map_centralizes q A (S : Subgroup G) hAC
  have hDtwo : IsPGroup 2 D := (S.isPGroup'.to_le hAS).map q
  have hDnot : D ≠ ⊥ := by
    intro hD
    have hAC' : A ≤ C := by
      simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff A).mp hD
    exact hnot (hAC'.trans hCcentral)
  let : Nontrivial D := Subgroup.nontrivial_iff_ne_bot D |>.mpr hDnot
  obtain ⟨k, hk, hcard⟩ := hDtwo.nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := D) 2
    (by rw [hcard]; exact dvd_pow_self 2 hk.ne')
  let zT : (T : Subgroup (G ⧸ C)) := ⟨(z : G ⧸ C), hDT z.property⟩
  have hzT : orderOf zT = 2 :=
    (Subgroup.orderOf_mk (z : G ⧸ C) (hDT z.property)).trans
      ((Subgroup.orderOf_coe z).trans hz)
  have hzTC : zT ∈ Subgroup.center (T : Subgroup (G ⧸ C)) := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hDC z.property) t t.property
  have hwcQ := weakClosure_map_quotient S C A hAS hwc
  have hzc := (CFSG.Adapters.glauberman_zStar T zT hzTC hzT
    (fun g hg => hwcQ z z.property g hg)).2
  have hbot : Function.Injective (QuotientGroup.mk' (CFSG.oddCore (G ⧸ C))) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', hQcore]
  have hzcentral : (z : G ⧸ C) ∈ Subgroup.center (G ⧸ C) :=
    Subgroup.comap_center_le_center hbot hzc
  let B : Subgroup G := (Subgroup.zpowers (z : G ⧸ C)).comap q
  have hzD : Subgroup.zpowers (z : G ⧸ C) ≤ D := Subgroup.zpowers_le.mpr z.property
  have hBA : B ≤ A := by
    have h := Subgroup.comap_mono (f := q) hzD
    change B ≤ (A.map q).comap q at h
    rw [Subgroup.comap_map_eq_self (show q.ker ≤ A from by
      simpa only [q, QuotientGroup.ker_mk'] using (inf_le_left : C ≤ A))] at h
    exact h
  let : IsCyclic B := Subgroup.isCyclic_of_le hBA
  let : (Subgroup.zpowers (z : G ⧸ C)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzcentral)
  let : B.Normal := inferInstance
  have hBC : B ≤ Subgroup.center G :=
    normal_cyclic_two_subgroup_central_of_sylow S B (hBA.trans hAS) (hBA.trans hAC)
  obtain ⟨b, hb, hq⟩ := Subgroup.mem_map.mp z.property
  have hbB : b ∈ B := by
    change q b ∈ Subgroup.zpowers (z : G ⧸ C)
    rw [hq]
    exact Subgroup.mem_zpowers _
  have hbC : b ∈ C := ⟨hb, hBC hbB⟩
  have hz1 : (z : G ⧸ C) = 1 := hq.symm.trans ((QuotientGroup.eq_one_iff b).mpr hbC)
  have hzone : z = 1 := Subtype.ext hz1
  rw [hzone, orderOf_one] at hz
  norm_num at hz

theorem weakClosure_transport_equiv
    {G : Type*} {H : Type*} [Group G] [Group H] [Finite G]
    {p : ℕ} [Fact p.Prime] (e : G ≃* H) (S : Sylow p G)
    (A : Subgroup G)
    (hwc : ∀ a ∈ A, ∀ g : G,
      g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g = a) :
    let T : Sylow p H := S.mapSurjective (f := e.toMonoidHom) e.surjective
    ∀ a ∈ A.map e.toMonoidHom, ∀ h : H,
      h⁻¹ * a * h ∈ (T : Subgroup H) → h⁻¹ * a * h = a := by
  let T : Sylow p H := S.mapSurjective (f := e.toMonoidHom) e.surjective
  change ∀ a ∈ A.map e.toMonoidHom, ∀ h : H,
    h⁻¹ * a * h ∈ (T : Subgroup H) → h⁻¹ * a * h = a
  rintro a ⟨b, hb, rfl⟩ h hh
  obtain ⟨g, rfl⟩ := e.surjective h
  have hmap : e (g⁻¹ * b * g) ∈ (S : Subgroup G).map e.toMonoidHom := by
    have hh' := hh
    change (e g)⁻¹ * e b * e g ∈ (T : Subgroup H) at hh'
    rw [show (T : Subgroup H) = (S : Subgroup G).map e.toMonoidHom from
      Sylow.coe_mapSurjective e.surjective S] at hh'
    rw [map_mul, map_mul, map_inv]
    exact hh'
  have hmem : g⁻¹ * b * g ∈ (S : Subgroup G) := by
    obtain ⟨s, hs, heq⟩ := hmap
    exact e.injective heq ▸ hs
  change (e g)⁻¹ * e b * e g = e b
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg e (hwc b hb g hmem)

@[expose] def weakClosureFiniteCarrier (G : Type*) [Finite G] : Type := Fin (Nat.card G)

theorem cyclic_weakClosure_central_of_oddCore_eq_bot_universe
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (A : Subgroup G) [IsCyclic A]
    (hAS : A ≤ (S : Subgroup G))
    (hAC : A ≤ Subgroup.centralizer (S : Set G))
    (hwc : ∀ a ∈ A, ∀ g : G,
      g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g = a)
    (hcore : CFSG.oddCore G = ⊥) : A ≤ Subgroup.center G := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype G := Fintype.ofFinite G
  let H := weakClosureFiniteCarrier G
  let e0 : H ≃ G :=
    (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)).symm
  let : Group H := e0.group
  let e1 : H ≃* G := e0.mulEquiv
  let e : G ≃* H := e1.symm
  let : Finite H := Finite.of_equiv G e0.symm
  let T : Sylow 2 H := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let D : Subgroup H := A.map e.toMonoidHom
  let : IsCyclic D := isCyclic_of_surjective (e.toMonoidHom.subgroupMap A)
    (e.toMonoidHom.subgroupMap_surjective A)
  have hDT : D ≤ (T : Subgroup H) := by
    rw [show (T : Subgroup H) = (S : Subgroup G).map e.toMonoidHom from
      Sylow.coe_mapSurjective e.surjective S]
    exact Subgroup.map_mono hAS
  have hDC : D ≤ Subgroup.centralizer (T : Set H) := by
    change D ≤ Subgroup.centralizer ((T : Subgroup H) : Set H)
    rw [show (T : Subgroup H) = (S : Subgroup G).map e.toMonoidHom from
      Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S]
    exact weakClosure_map_centralizes e.toMonoidHom A (S : Subgroup G) hAC
  have hHcore : CFSG.oddCore H = ⊥ := by
    rw [weakClosure_oddCore_eq_pPrimeCore] at hcore ⊢
    rw [← CFSG.pPrimeCore_map_iso 2 e, hcore, Subgroup.map_bot]
  have hcentral := cyclic_weakClosure_central_of_oddCore_eq_bot T D hDT hDC
    (weakClosure_transport_equiv e S A hwc) hHcore
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro g
  apply e.injective
  have h := Subgroup.mem_center_iff.mp
    (hcentral (Subgroup.mem_map_of_mem e.toMonoidHom ha)) (e g)
  change e g * e a = e a * e g at h
  rw [map_mul, map_mul]
  exact h



theorem cyclic_weakClosure_image_central_mod_oddCore
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (A : Subgroup G) [IsCyclic A]
    (hAS : A ≤ (S : Subgroup G))
    (hAC : A ≤ Subgroup.centralizer (S : Set G))
    (hwc : ∀ a ∈ A, ∀ g : G,
      g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g = a) :
    A.map (QuotientGroup.mk' (CFSG.oddCore G)) ≤
      Subgroup.center (G ⧸ CFSG.oddCore G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R := CFSG.oddCore G
  let q := QuotientGroup.mk' R
  let T := S.mapSurjective (QuotientGroup.mk'_surjective R)
  let D := A.map q
  let : IsCyclic D := isCyclic_of_surjective (q.subgroupMap A) (q.subgroupMap_surjective A)
  have hDT : D ≤ (T : Subgroup (G ⧸ R)) := by
    simpa only [T, Sylow.coe_mapSurjective] using (Subgroup.map_mono (f := q) hAS)
  have hDC : D ≤ Subgroup.centralizer (T : Set (G ⧸ R)) := by
    change D ≤ Subgroup.centralizer ((T : Subgroup (G ⧸ R)) : Set (G ⧸ R))
    rw [show (T : Subgroup (G ⧸ R)) = (S : Subgroup G).map q from
      Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective R) S]
    exact weakClosure_map_centralizes q A (S : Subgroup G) hAC
  exact cyclic_weakClosure_central_of_oddCore_eq_bot_universe T D hDT hDC
    (weakClosure_map_quotient S R A hAS hwc) (weakClosure_oddCore_quotient_eq_bot G)

theorem weakClosure_normal_centralizer_factorization
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (A R : Subgroup G) [R.Normal]
    (hAS : A ≤ (S : Subgroup G))
    (hwc : ∀ a ∈ A, ∀ g : G,
      g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g = a)
    (hcen : A.map (QuotientGroup.mk' R) ≤ Subgroup.center (G ⧸ R)) :
    ∀ g : G, ∃ r ∈ R, ∃ c ∈ Subgroup.centralizer (A : Set G), g = r * c := by
  intro g
  let q := QuotientGroup.mk' R
  let f := (MulAut.conj g⁻¹).toMonoidHom
  let P := A.map f
  have hP : IsPGroup p P := (S.isPGroup'.to_le hAS).map f
  have hPRS : P ≤ R ⊔ (S : Subgroup G) := by
    rintro x ⟨a, ha, rfl⟩
    have hacen := hcen (Subgroup.mem_map_of_mem q ha)
    have hcomm := Subgroup.mem_center_iff.mp hacen (q g)
    have hqeq : q (f a) = q a := by
      change q (g⁻¹ * a * (g⁻¹)⁻¹) = q a
      rw [inv_inv, map_mul, map_mul, map_inv, mul_assoc, ← hcomm,
        ← mul_assoc, inv_mul_cancel, one_mul]
    have hmap : q (f a) ∈ (S : Subgroup G).map q := by
      rw [hqeq]
      exact Subgroup.mem_map_of_mem q (hAS ha)
    have hpre : f a ∈ ((S : Subgroup G).map q).comap q := hmap
    simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk', sup_comm] using hpre
  obtain ⟨r, hr, hcon⟩ := pSubgroup_conjugate_into_sylow_by_normal S R P hP hPRS
  have hcentral : g * r ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hmem : (g * r)⁻¹ * a * (g * r) ∈ (S : Subgroup G) := by
      have h := hcon (f a) (Subgroup.mem_map_of_mem f ha)
      change r⁻¹ * (g⁻¹ * a * (g⁻¹)⁻¹) * r ∈ (S : Subgroup G) at h
      simpa only [inv_inv, mul_inv_rev, mul_assoc] using h
    have heq := hwc a ha (g * r) hmem
    calc
      a * (g * r) = (g * r) * ((g * r)⁻¹ * a * (g * r)) := by group
      _ = (g * r) * a := by rw [heq]
  refine ⟨g * r⁻¹ * g⁻¹,
    Subgroup.Normal.conj_mem inferInstance r⁻¹ (R.inv_mem hr) g,
    g * r, hcentral, ?_⟩
  group

theorem cyclic_weakly_closed_central_sylow_subgroup_central_mod_odd_core
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (A : Subgroup G) [IsCyclic A]
    (hAS : A ≤ (S : Subgroup G))
    (hAC : A ≤ Subgroup.centralizer (S : Set G))
    (hwc : ∀ a ∈ A, ∀ g : G,
      g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g = a) :
    A.map (QuotientGroup.mk' (CFSG.oddCore G)) ≤
      Subgroup.center (G ⧸ CFSG.oddCore G) ∧
    (∀ g : G, ∃ r ∈ CFSG.oddCore G,
      ∃ c ∈ Subgroup.centralizer (A : Set G), g = r * c) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen := cyclic_weakClosure_image_central_mod_oddCore S A hAS hAC hwc
  exact ⟨hcen, weakClosure_normal_centralizer_factorization S A (CFSG.oddCore G) hAS hwc hcen⟩


end CFSG.Wreathed
