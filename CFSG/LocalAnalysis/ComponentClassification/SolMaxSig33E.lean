module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33C
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32H
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33B

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {x : G} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : IsPGroup 2 (zpowers x) := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem exists_fixed_component_of_acts [Finite X] {C J : Subgroup X} {n : ℕ} (hJC : J ≤ C)
    (hJpc : IsPComponent 2 (J.subgroupOf C))
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) {c e : X}
    (hcN : c ∈ normalizer (J : Set X)) (hc2 : c * c = 1) (he : e ∈ J)
    (hce : c * e⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (h5 : 5 ≤ n - (coreImage θ he).support.card) :
    ∃ Je : Subgroup X, Je ≤ J ⊓ centralizer ({c} : Set X) ∧
      IsPComponent 2 (Je.subgroupOf (C ⊓ centralizer ({c} : Set X))) ∧
      (∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (coreImage θ hx).support ⊆ (coreImage θ he).supportᶜ → x ∈ Je) ∧
      (∀ x ∈ Je, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he).supportᶜ) ∧
      ∃ χ : ↥Je ⧸ pPrimeCore 2 ↥Je ≃*
          alternatingGroup ↥((coreImage θ he).supportᶜ : Finset (Fin n)),
        ∀ (x : ↥Je) (hx : (x : X) ∈ J),
          Perm.ofSubtype ((χ (x : ↥Je ⧸ pPrimeCore 2 ↥Je) : alternatingGroup _) :
            Perm ↥((coreImage θ he).supportᶜ : Finset (Fin n))) = coreImage θ hx := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Oj := pPrimeCore 2 ↥J with hOjdef
  set e' : ↥J := ⟨e, he⟩ with he'def
  set τ' : alternatingGroup (Fin n) := θ (e' : ↥J ⧸ Oj) with hτ'def
  set τ : Perm (Fin n) := coreImage θ he with hτdef
  have hττ' : τ = (τ' : Perm (Fin n)) := rfl
  have hτA : τ ∈ alternatingGroup (Fin n) := τ'.2
  set cJ : MulAut ↥J := J.normalizerMonoidHom ⟨c, hcN⟩ with hcJdef
  have hcJapp : ∀ x : ↥J, ((cJ x : ↥J) : X) = c * x * c⁻¹ := fun x => rfl
  have hlike : ∀ x : ↥J, θ ((cJ x : ↥J) : ↥J ⧸ Oj) = τ' * θ (x : ↥J ⧸ Oj) * τ'⁻¹ := by
    intro x
    set u := c * e⁻¹ with hudef
    have hu := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hce)).2 (e * x * e⁻¹)
      (mul_mem (mul_mem he x.2) (inv_mem he))
    rw [inv_inv] at hu
    obtain ⟨o, ho, hoeq⟩ := hu
    have hoeq' : (o : X) = (e * x * e⁻¹)⁻¹ * u * (e * x * e⁻¹) * u⁻¹ := hoeq
    have h1 : cJ x = e' * x * e'⁻¹ * o := by
      apply Subtype.ext
      rw [hcJapp]
      change c * (x : X) * c⁻¹ = e * x * e⁻¹ * (o : X)
      rw [hoeq', hudef]
      group
    rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).mpr ho, mul_one,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv]
  set G := J ⊓ centralizer ({c} : Set X) with hGdef
  set H := centralizer ({τ'} : Set (alternatingGroup (Fin n))) with hHdef
  have hGJ : G ≤ J := inf_le_left
  set q₀ : ↥G →* alternatingGroup (Fin n) :=
    (θ.toMonoidHom.comp (QuotientGroup.mk' Oj)).comp (inclusion hGJ) with hq₀def
  have hq₀ : ∀ x : ↥G, q₀ x = θ ((inclusion hGJ x : ↥J) : ↥J ⧸ Oj) := fun _ => rfl
  have hq₀H : ∀ x : ↥G, q₀ x ∈ H := by
    intro x
    rw [mem_centralizer_singleton_iff, hq₀]
    have hxc : cJ (inclusion hGJ x) = inclusion hGJ x := by
      apply Subtype.ext
      rw [hcJapp]
      have h1 : ((x : X)) * c = c * x := mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2
      change c * (x : X) * c⁻¹ = x
      rw [← h1]
      group
    have h2 := hlike (inclusion hGJ x)
    rw [hxc] at h2
    calc θ ((inclusion hGJ x : ↥J) : ↥J ⧸ Oj) * τ' =
        (τ' * θ ((inclusion hGJ x : ↥J) : ↥J ⧸ Oj) * τ'⁻¹) * τ' := by rw [← h2]
      _ = τ' * θ ((inclusion hGJ x : ↥J) : ↥J ⧸ Oj) := by group
  set q : ↥G →* ↥H := q₀.codRestrict H hq₀H with hqdef
  have hqs : Function.Surjective q := by
    rintro ⟨h, hh⟩
    obtain ⟨y, rfl⟩ := θ.surjective h
    obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective y
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    have hc : ∀ x, cJ (cJ x) = x := by
      intro x
      apply Subtype.ext
      rw [hcJapp, hcJapp, hcinv]
      calc c * (c * (x : X) * c) * c = (c * c) * x * (c * c) := by group
        _ = x := by rw [hc2]; group
    have hw : ((cJ w₀ : ↥J) : ↥J ⧸ Oj) = (w₀ : ↥J ⧸ Oj) := by
      apply θ.injective
      rw [hlike]
      have hh' : θ (w₀ : ↥J ⧸ Oj) * τ' = τ' * θ (w₀ : ↥J ⧸ Oj) :=
        mem_centralizer_singleton_iff.mp hh
      rw [← hh']
      group
    obtain ⟨w, hwc, hww⟩ := exists_fixed_of_mk_eq cJ hc hw
    have hwe : (w : X) * c = c * w := by
      have h1 := congrArg Subtype.val hwc
      rw [hcJapp] at h1
      calc (w : X) * c = c * w * c⁻¹ * c := by rw [h1]
        _ = c * w := by group
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
  have hFH : fixAlt τ ≤ H := fixAlt_le_centralizer hτA
  have hFcomp := isComponent_fixAlt hτA h5
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
  set Je := L.map G.subtype with hJedef
  have hJeG : Je ≤ G := map_subtype_le _
  have hJeJ : Je ≤ J := hJeG.trans hGJ
  have hLpc : IsPComponent 2 (Je.subgroupOf G) := by
    change IsPComponent 2 ((L.map G.subtype).comap G.subtype)
    rw [comap_map_eq_self_of_injective G.subtype_injective]
    exact (CatalogueBAlternating.pComponent_two_iff _).mpr hL
  have hGsub :
      (G.subgroupOf (C ⊓ centralizer ({c} : Set X))).IsSubnormal := by
    have hJsub : (J.subgroupOf C).IsSubnormal := hJpc.choose_spec.2.1
    have h1 : G.subgroupOf (C ⊓ centralizer ({c} : Set X)) =
        (J.subgroupOf C).comap (inclusion inf_le_left) := by
      ext x
      simp only [mem_subgroupOf, mem_comap, coe_inclusion, hGdef, mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp x.2).2⟩⟩
    rw [h1]
    exact hJsub.comap _
  have hGC : G ≤ C ⊓ centralizer ({c} : Set X) :=
    le_inf (hGJ.trans hJC) inf_le_right
  have hJepc : IsPComponent 2
      (Je.subgroupOf (C ⊓ centralizer ({c} : Set X))) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hJeG hGC hGsub).mpr hLpc
  have hmemQ : ∀ x : ↥G, ((q x : ↥H) : alternatingGroup (Fin n)) ∈ fixAlt τ →
      x ∈ (L.map q).comap q := by
    intro x hx
    rw [mem_comap, hLmap]
    exact hx
  have hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ τ.supportᶜ → x ∈ Je := by
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
  have hsubP : ∀ x ∈ Je, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ τ.supportᶜ := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨hGJ l.2, ?_⟩
    have h1 : q l ∈ Q := by rw [← hLmap]; exact ⟨l, hl, rfl⟩
    exact mem_fixAlt.mp h1
  obtain ⟨φ, hφ⟩ := exists_fixAlt_equiv τ
  set r₀ : ↥Je →* alternatingGroup (Fin n) :=
    (θ.toMonoidHom.comp (QuotientGroup.mk' Oj)).comp (inclusion hJeJ) with hr₀def
  have hr₀ : ∀ x : ↥Je, r₀ x = θ ((inclusion hJeJ x : ↥J) : ↥J ⧸ Oj) := fun _ => rfl
  have hr₀F : ∀ x : ↥Je, r₀ x ∈ fixAlt τ := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩
    have h1 : q l ∈ Q := by rw [← hLmap]; exact ⟨l, hl, rfl⟩
    exact h1
  set r : ↥Je →* alternatingGroup ↥(τ.supportᶜ : Finset (Fin n)) :=
    φ.symm.toMonoidHom.comp (r₀.codRestrict (fixAlt τ) hr₀F) with hrdef
  have hrs : Function.Surjective r := by
    intro b
    set b' := φ b with hb'def
    have hb'H : (b' : alternatingGroup (Fin n)) ∈ H := hFH b'.2
    have hb'Q : (⟨b', hb'H⟩ : ↥H) ∈ Q := b'.2
    rw [← hLmap] at hb'Q
    obtain ⟨l, hl, hlb⟩ := hb'Q
    refine ⟨⟨G.subtype l, l, hl, rfl⟩, ?_⟩
    apply φ.injective
    change φ (φ.symm _) = b'
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change ((q l : ↥H) : alternatingGroup (Fin n)) = (b' : alternatingGroup (Fin n))
    rw [hlb]
  have hrk : Odd (Nat.card r.ker) := by
    let g : r.ker →* Oj :=
      ((inclusion hJeJ).comp r.ker.subtype).codRestrict Oj fun x => by
        have h1 : r (x : ↥Je) = 1 := x.2
        have h2 : r₀ (x : ↥Je) = 1 := by
          have h3 : (r₀.codRestrict (fixAlt τ) hr₀F) (x : ↥Je) = 1 := by
            apply φ.symm.injective
            rw [map_one]
            exact h1
          exact congrArg Subtype.val h3
        rwa [hr₀, map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at h2
    have hg : Function.Injective g := fun x y h => by
      have h' : (((x : ↥Je) : X)) = ((y : ↥Je) : X) :=
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
  refine ⟨Je, hJeG, hJepc, hinv, hsubP, (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective r hrs), fun x hx => ?_⟩
  have hχ : (QuotientGroup.quotientKerEquivOfSurjective r hrs) (x : ↥Je ⧸ r.ker) = r x :=
    QuotientGroup.kerLift_mk r x
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk, hχ]
  have h1 : r x = φ.symm (r₀.codRestrict (fixAlt τ) hr₀F x) := rfl
  rw [h1, ← hφ, MulEquiv.apply_symm_apply]
  show ((r₀ x : alternatingGroup (Fin n)) : Perm (Fin n)) = coreImage θ hx
  rw [hr₀]
  rfl

end CFSG.ComponentClassification.SolMax
