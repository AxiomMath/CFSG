module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33E

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem fixAlt_le_comap_centralizer {n : ℕ} (τ : Perm (Fin n)) :
    fixAlt τ ≤
      (centralizer ({τ} : Set (Perm (Fin n)))).comap (alternatingGroup (Fin n)).subtype := by
  intro k hk
  rw [mem_comap, mem_centralizer_singleton_iff]
  have hd : (k : Perm (Fin n)).Disjoint τ := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    exact Disjoint.mono_left (mem_fixAlt.mp hk) disjoint_compl_left
  exact hd.commute.eq

theorem isComponent_fixAlt_comap {n : ℕ} {τ : Perm (Fin n)} (h5 : 5 ≤ n - τ.support.card) :
    IsComponent ((fixAlt τ).subgroupOf
      ((centralizer ({τ} : Set (Perm (Fin n)))).comap (alternatingGroup (Fin n)).subtype)) := by
  classical
  set C := (centralizer ({τ} : Set (Perm (Fin n)))).comap (alternatingGroup (Fin n)).subtype
    with hC
  have hle : fixAlt τ ≤ C := fixAlt_le_comap_centralizer τ
  have hcard : 5 ≤ Nat.card ↥(τ.supportᶜ : Finset (Fin n)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    exact h5
  have : IsSimpleGroup (alternatingGroup ↥(τ.supportᶜ : Finset (Fin n))) :=
    alternatingGroup.isSimpleGroup hcard
  have hq := (LocalCores.isQuasisimple_of_isSimpleGroup
    (alt_nonabelian_of_card (Ω := ↥(τ.supportᶜ : Finset (Fin n))) (by omega))).1
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv
    ((fixAltEquiv τ).trans (subgroupOfEquivOfLe hle).symm) hq, ?_⟩
  refine Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hle).mpr fun c hc => ?_)
  have hc' : (c : Perm (Fin n)) * τ = τ * c := mem_centralizer_singleton_iff.mp hc
  rw [mem_normalizer_iff]
  intro k
  constructor
  · exact conj_mem_fixAlt hc'
  · intro hk
    have hci : ((c⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) * τ = τ * (c⁻¹ :) := by
      have h1 : (c : Perm (Fin n))⁻¹ * τ = τ * (c : Perm (Fin n))⁻¹ := by
        calc (c : Perm (Fin n))⁻¹ * τ =
            (c : Perm (Fin n))⁻¹ * (τ * c) * (c : Perm (Fin n))⁻¹ := by group
          _ = (c : Perm (Fin n))⁻¹ * (c * τ) * (c : Perm (Fin n))⁻¹ := by rw [hc']
          _ = τ * (c : Perm (Fin n))⁻¹ := by group
      exact h1
    have h2 := conj_mem_fixAlt hci hk
    rwa [show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group] at h2

variable {X : Type} [Group X]

theorem exists_fixed_component_of_perm [Finite X] {C J : Subgroup X} {n : ℕ} (hJC : J ≤ C)
    (hJpc : IsPComponent 2 (J.subgroupOf C))
    {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction θ ρJ) {b : X}
    (hbN : b ∈ normalizer (J : Set X)) (hb2 : b * b = 1)
    (h5 : 5 ≤ n - (ρJ ⟨b, hbN⟩).support.card) :
    ∃ Jb : Subgroup X, Jb ≤ J ⊓ centralizer ({b} : Set X) ∧
      IsPComponent 2 (Jb.subgroupOf (C ⊓ centralizer ({b} : Set X))) ∧
      (∀ (x : X) (hx : x ∈ J), x * b = b * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (coreImage θ hx).support ⊆ (ρJ ⟨b, hbN⟩).supportᶜ → x ∈ Jb) ∧
      (∀ x ∈ Jb, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (ρJ ⟨b, hbN⟩).supportᶜ) ∧
      ∃ χ : ↥Jb ⧸ pPrimeCore 2 ↥Jb ≃*
          alternatingGroup ↥((ρJ ⟨b, hbN⟩).supportᶜ : Finset (Fin n)),
        ∀ (x : ↥Jb) (hx : (x : X) ∈ J),
          Perm.ofSubtype ((χ (x : ↥Jb ⧸ pPrimeCore 2 ↥Jb) : alternatingGroup _) :
            Perm ↥((ρJ ⟨b, hbN⟩).supportᶜ : Finset (Fin n))) = coreImage θ hx := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Oj := pPrimeCore 2 ↥J with hOjdef
  set τ : Perm (Fin n) := ρJ ⟨b, hbN⟩ with hτdef
  set cJ : MulAut ↥J := J.normalizerMonoidHom ⟨b, hbN⟩ with hcJdef
  have hcJapp : ∀ x : ↥J, ((cJ x : ↥J) : X) = b * x * b⁻¹ := fun x => rfl
  have hlike : ∀ x : ↥J, (θ ((cJ x : ↥J) : ↥J ⧸ Oj) : Perm (Fin n)) =
      τ * (θ (x : ↥J ⧸ Oj) : Perm (Fin n)) * τ⁻¹ := fun x => hρJ ⟨b, hbN⟩ x
  set G := J ⊓ centralizer ({b} : Set X) with hGdef
  set H := (centralizer ({τ} : Set (Perm (Fin n)))).comap (alternatingGroup (Fin n)).subtype
    with hHdef
  have hmemH : ∀ h : alternatingGroup (Fin n), h ∈ H ↔ (h : Perm (Fin n)) * τ = τ * h := by
    intro h
    rw [hHdef, mem_comap, mem_centralizer_singleton_iff]
    exact ⟨fun h1 => h1, fun h1 => h1⟩
  have hGJ : G ≤ J := inf_le_left
  set q₀ : ↥G →* alternatingGroup (Fin n) :=
    (θ.toMonoidHom.comp (QuotientGroup.mk' Oj)).comp (inclusion hGJ) with hq₀def
  have hq₀ : ∀ x : ↥G, q₀ x = θ ((inclusion hGJ x : ↥J) : ↥J ⧸ Oj) := fun _ => rfl
  have hq₀H : ∀ x : ↥G, q₀ x ∈ H := by
    intro x
    rw [hmemH, hq₀]
    have hxc : cJ (inclusion hGJ x) = inclusion hGJ x := by
      apply Subtype.ext
      rw [hcJapp]
      have h1 : ((x : X)) * b = b * x := mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2
      change b * (x : X) * b⁻¹ = x
      rw [← h1]
      group
    have h2 := hlike (inclusion hGJ x)
    rw [hxc] at h2
    calc (θ ((inclusion hGJ x : ↥J) : ↥J ⧸ Oj) : Perm (Fin n)) * τ =
        (τ * (θ ((inclusion hGJ x : ↥J) : ↥J ⧸ Oj) : Perm (Fin n)) * τ⁻¹) * τ := by
          rw [← h2]
      _ = τ * (θ ((inclusion hGJ x : ↥J) : ↥J ⧸ Oj) : Perm (Fin n)) := by group
  set q : ↥G →* ↥H := q₀.codRestrict H hq₀H with hqdef
  have hqs : Function.Surjective q := by
    rintro ⟨h, hh⟩
    obtain ⟨y, rfl⟩ := θ.surjective h
    obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective y
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hc : ∀ x, cJ (cJ x) = x := by
      intro x
      apply Subtype.ext
      rw [hcJapp, hcJapp, hbinv]
      calc b * (b * (x : X) * b) * b = (b * b) * x * (b * b) := by group
        _ = x := by rw [hb2]; group
    have hw : ((cJ w₀ : ↥J) : ↥J ⧸ Oj) = (w₀ : ↥J ⧸ Oj) := by
      apply θ.injective
      apply Subtype.ext
      rw [hlike]
      have hh' : (θ (w₀ : ↥J ⧸ Oj) : Perm (Fin n)) * τ = τ * (θ (w₀ : ↥J ⧸ Oj) : Perm (Fin n)) :=
        (hmemH _).mp hh
      rw [← hh']
      group
    obtain ⟨w, hwc, hww⟩ := exists_fixed_of_mk_eq cJ hc hw
    have hwe : (w : X) * b = b * w := by
      have h1 := congrArg Subtype.val hwc
      rw [hcJapp] at h1
      calc (w : X) * b = b * w * b⁻¹ * b := by rw [h1]
        _ = b * w := by group
    refine ⟨⟨w, w.2, mem_centralizer_singleton_iff.mpr hwe⟩, Subtype.ext ?_⟩
    change θ ((⟨(w : X), w.2⟩ : ↥J) : ↥J ⧸ Oj) = θ (w₀ : ↥J ⧸ Oj)
    rw [← hww]
  have hqk : Odd (Nat.card q.ker) := by
    let g : q.ker →* Oj :=
      ((inclusion hGJ).comp q.ker.subtype).codRestrict Oj fun x => by
        have h1 : q (x : ↥G) = 1 := x.2
        have h2 : θ ((inclusion hGJ (x : ↥G) : ↥J) : ↥J ⧸ Oj) = 1 := congrArg Subtype.val h1
        rwa [map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at h2
    have hg : Function.Injective g := fun x y h => by
      have h' : (((x : ↥G) : X)) = ((y : ↥G) : X) := congrArg (fun z : Oj => ((z : ↥J) : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (Subgroup.card_dvd_of_injective g hg)
  have hFH : fixAlt τ ≤ H := fixAlt_le_comap_centralizer τ
  have hFcomp := isComponent_fixAlt_comap h5
  set Q : Subgroup ↥H := (fixAlt τ).subgroupOf H with hQdef
  have hFsimple := isSimpleGroup_fixAlt h5
  have hFnab : ∃ a b : ↥(fixAlt τ), a * b ≠ b * a := by
    obtain ⟨φ, -⟩ := exists_fixAlt_equiv τ
    obtain ⟨a, b, hab⟩ := alt_nonabelian_of_card (Ω := ↥(τ.supportᶜ : Finset (Fin n))) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
      omega)
    exact ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩
  have hFeven : Even (Nat.card ↥(fixAlt τ)) := by
    obtain ⟨φ, -⟩ := exists_fixAlt_equiv τ
    rw [← Nat.card_congr φ.toEquiv]
    exact even_card_alternatingGroup (by
      rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
      omega)
  have hQpc : IsPComponent 2 Q :=
    isPComponent_subgroupOf_of_simple hFH hFcomp.2 hFsimple hFnab hFeven
  obtain ⟨L, hL, hLmap⟩ := OddKernelTwoComponents.exists_lift q hqs hqk Q
    ((CatalogueBAlternating.pComponent_two_iff _).mp hQpc)
  set Jb := L.map G.subtype with hJbdef
  have hJbG : Jb ≤ G := map_subtype_le _
  have hJbJ : Jb ≤ J := hJbG.trans hGJ
  have hLpc : IsPComponent 2 (Jb.subgroupOf G) := by
    change IsPComponent 2 ((L.map G.subtype).comap G.subtype)
    rw [comap_map_eq_self_of_injective G.subtype_injective]
    exact (CatalogueBAlternating.pComponent_two_iff _).mpr hL
  have hGsub :
      (G.subgroupOf (C ⊓ centralizer ({b} : Set X))).IsSubnormal := by
    have hJsub : (J.subgroupOf C).IsSubnormal := hJpc.choose_spec.2.1
    have h1 : G.subgroupOf (C ⊓ centralizer ({b} : Set X)) =
        (J.subgroupOf C).comap (inclusion inf_le_left) := by
      ext x
      simp only [mem_subgroupOf, mem_comap, coe_inclusion, hGdef, mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp x.2).2⟩⟩
    rw [h1]
    exact hJsub.comap _
  have hGC : G ≤ C ⊓ centralizer ({b} : Set X) :=
    le_inf (hGJ.trans hJC) inf_le_right
  have hJbpc : IsPComponent 2
      (Jb.subgroupOf (C ⊓ centralizer ({b} : Set X))) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hJbG hGC hGsub).mpr hLpc
  have hmemQ : ∀ x : ↥G, ((q x : ↥H) : alternatingGroup (Fin n)) ∈ fixAlt τ →
      x ∈ (L.map q).comap q := by
    intro x hx
    rw [mem_comap, hLmap]
    exact hx
  have hinv : ∀ (x : X) (hx : x ∈ J), x * b = b * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ τ.supportᶜ → x ∈ Jb := by
    intro x hx hxe hxx hxs
    set xG : ↥G := ⟨x, hx, mem_centralizer_singleton_iff.mpr hxe⟩ with hxGdef
    have hxQ : xG ∈ (L.map q).comap q := hmemQ xG (mem_fixAlt.mpr hxs)
    have hres := OddKernelTwoComponents.lift_subgroupOf_eq_residual q hqs hqk L hL
    have hxL : (⟨xG, hxQ⟩ : ↥((L.map q).comap q)) ∈ L.subgroupOf ((L.map q).comap q) := by
      rw [hres]
      obtain ⟨k, hk⟩ := hxx
      have hxx' : (⟨xG, hxQ⟩ : ↥((L.map q).comap q)) ^ 2 ^ k = 1 :=
        Subtype.ext (Subtype.ext (by simpa using hk))
      exact TwoResidual.twoSubgroup_le _ (isPGroup_zpowers_of_pow_eq_one hxx') (mem_zpowers _)
    exact ⟨xG, hxL, rfl⟩
  have hsubP : ∀ x ∈ Jb, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ τ.supportᶜ := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨hGJ l.2, ?_⟩
    have h1 : q l ∈ Q := by rw [← hLmap]; exact ⟨l, hl, rfl⟩
    exact mem_fixAlt.mp h1
  obtain ⟨φ, hφ⟩ := exists_fixAlt_equiv τ
  set r₀ : ↥Jb →* alternatingGroup (Fin n) :=
    (θ.toMonoidHom.comp (QuotientGroup.mk' Oj)).comp (inclusion hJbJ) with hr₀def
  have hr₀ : ∀ x : ↥Jb, r₀ x = θ ((inclusion hJbJ x : ↥J) : ↥J ⧸ Oj) := fun _ => rfl
  have hr₀F : ∀ x : ↥Jb, r₀ x ∈ fixAlt τ := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩
    have h1 : q l ∈ Q := by rw [← hLmap]; exact ⟨l, hl, rfl⟩
    exact h1
  set r : ↥Jb →* alternatingGroup ↥(τ.supportᶜ : Finset (Fin n)) :=
    φ.symm.toMonoidHom.comp (r₀.codRestrict (fixAlt τ) hr₀F) with hrdef
  have hrs : Function.Surjective r := by
    intro b'
    set b'' := φ b' with hb''def
    have hb''H : (b'' : alternatingGroup (Fin n)) ∈ H := hFH b''.2
    have hb''Q : (⟨b'', hb''H⟩ : ↥H) ∈ Q := b''.2
    rw [← hLmap] at hb''Q
    obtain ⟨l, hl, hlb⟩ := hb''Q
    refine ⟨⟨G.subtype l, l, hl, rfl⟩, ?_⟩
    apply φ.injective
    change φ (φ.symm _) = b''
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change ((q l : ↥H) : alternatingGroup (Fin n)) = (b'' : alternatingGroup (Fin n))
    rw [hlb]
  have hrk : Odd (Nat.card r.ker) := by
    let g : r.ker →* Oj :=
      ((inclusion hJbJ).comp r.ker.subtype).codRestrict Oj fun x => by
        have h1 : r (x : ↥Jb) = 1 := x.2
        have h2 : r₀ (x : ↥Jb) = 1 := by
          have h3 : (r₀.codRestrict (fixAlt τ) hr₀F) (x : ↥Jb) = 1 := by
            apply φ.symm.injective
            rw [map_one]
            exact h1
          exact congrArg Subtype.val h3
        rwa [hr₀, map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at h2
    have hg : Function.Injective g := fun x y h => by
      have h' : (((x : ↥Jb) : X)) = ((y : ↥Jb) : X) :=
        congrArg (fun z : Oj => ((z : ↥J) : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (Subgroup.card_dvd_of_injective g hg)
  have hcard5 : 5 ≤ Nat.card ↥(τ.supportᶜ : Finset (Fin n)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  have : IsSimpleGroup (alternatingGroup ↥(τ.supportᶜ : Finset (Fin n))) :=
    alternatingGroup.isSimpleGroup hcard5
  have hAeven : Even (Nat.card (alternatingGroup ↥(τ.supportᶜ : Finset (Fin n)))) :=
    even_card_alternatingGroup (by
      rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
      omega)
  have hker := pPrimeCore_eq_ker r hrs hrk hAeven
  refine ⟨Jb, hJbG, hJbpc, hinv, hsubP, (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective r hrs), fun x hx => ?_⟩
  have hχ : (QuotientGroup.quotientKerEquivOfSurjective r hrs) (x : ↥Jb ⧸ r.ker) = r x :=
    QuotientGroup.kerLift_mk r x
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk, hχ]
  have h1 : r x = φ.symm (r₀.codRestrict (fixAlt τ) hr₀F x) := rfl
  rw [h1, ← hφ, MulEquiv.apply_symm_apply]
  show ((r₀ x : alternatingGroup (Fin n)) : Perm (Fin n)) = coreImage θ hx
  rw [hr₀]
  rfl

end CFSG.ComponentClassification.SolMax
