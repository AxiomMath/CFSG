module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisHomC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.GroupTheory.WeirSylow

section Kernel

variable {p a n : ℕ}

theorem homC_pow_p_pow (x : HomC p a n) : x ^ (p ^ a) = 1 := by
  funext i
  apply Multiplicative.toAdd.injective
  rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem homC_card_torsion_le_pow (hp : p.Prime) :
    Nat.card {x : HomC p a n // x ^ p = 1} ≤ p ^ n := by
  have e : {x : HomC p a n // x ^ p = 1} ≃
      (Fin n → {c : Multiplicative (ZMod (p ^ a)) // c ^ p = 1}) :=
    (Equiv.subtypeEquivRight (fun x => by
      constructor
      · intro h i
        exact congrFun h i
      · intro h
        exact funext h)).trans
      (Equiv.subtypePiEquivPi (p := fun _ c => c ^ p = 1))
  rw [Nat.card_congr e, Nat.card_pi]
  calc ∏ _i : Fin n, Nat.card {c : Multiplicative (ZMod (p ^ a)) // c ^ p = 1}
      ≤ ∏ _i : Fin n, p := Finset.prod_le_prod' (fun i _ => zmod_card_torsion_le hp)
    _ = p ^ n := by simp

theorem mem_zpowers_of_card_torsion_le {C : Type*} [Group C] [Finite C] (hp : p.Prime)
    (hC : Nat.card {c : C // c ^ p = 1} ≤ p) {g : C} (hg : orderOf g = p) {c : C}
    (hc : c ^ p = 1) : c ∈ Subgroup.zpowers g := by
  by_contra hnot
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hz : ∀ z : Subgroup.zpowers g, (z : C) ^ p = 1 := by
    rintro ⟨z, hz⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    change (g ^ m) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgp, one_zpow]
  let f : (Subgroup.zpowers g) ⊕ Unit → {x : C // x ^ p = 1} :=
    Sum.elim (fun z => ⟨(z : C), hz z⟩) (fun _ => ⟨c, hc⟩)
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with z | u <;> rcases b with w | u' <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr] at hab
    · have h : (z : C) = (w : C) := congrArg (fun t : {x : C // x ^ p = 1} => (t : C)) hab
      exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have h : (z : C) = c := congrArg (fun t : {x : C // x ^ p = 1} => (t : C)) hab
      exact hnot (h ▸ z.2)
    · exfalso
      have h : c = (w : C) := congrArg (fun t : {x : C // x ^ p = 1} => (t : C)) hab
      exact hnot (h ▸ w.2)
    · rfl
  have h1 := Nat.card_le_card_of_injective f hf
  have hc : Nat.card ((Subgroup.zpowers g) ⊕ Unit) = p + 1 := by
    rw [Nat.card_sum, Nat.card_zpowers, hg, Nat.card_unique]
  omega

theorem heis_ker_data (hp : p.Prime) (ha : 1 ≤ a) {P M : Type*} [Group P] [Group M]
    (e : P ≃* HomC p a n) (φ : P →* M) (hcyc : IsCyclic φ.range)
    (hcard : Nat.card φ.range = p ^ a) :
    (∀ x ∈ φ.ker, ∀ y ∈ φ.ker, x * y = y * x) ∧
    (n ≤ 2 → Nat.card {x : φ.ker // x ^ p = 1} ≤ p) ∧
    (2 ≤ a → ∀ x ∈ φ.ker, x ^ p = 1 → ∃ y ∈ φ.ker, y ^ p = x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have Pcomm : ∀ x y : P, x * y = y * x := fun x y =>
    e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hexp : ∀ x : P, x ^ (p ^ a) = 1 := fun x =>
    e.injective (by rw [map_pow, map_one]; exact homC_pow_p_pow _)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgord : orderOf g = p ^ a := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨u, hu⟩ : ∃ u : P, φ u = (g : M) := g.2
  have hφuord : orderOf (φ u) = p ^ a := by
    rw [hu, Subgroup.orderOf_coe, hgord]
  set z : P := u ^ (p ^ (a - 1)) with hz
  have hzp : z ^ p = 1 := by
    rw [hz, ← pow_mul, ← pow_succ, Nat.sub_add_cancel ha]
    exact hexp u
  have hφz : orderOf (φ z) = p := by
    rw [hz, map_pow]
    have hdvd : p ^ (a - 1) ∣ orderOf (φ u) := by
      rw [hφuord]
      exact pow_dvd_pow p (by omega)
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hφuord]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.pos b)]
  refine ⟨fun x _ y _ => Pcomm x y, ?_, ?_⟩
  ·
    intro hn
    let Ω : Subgroup P := torsionSubgroup (⊤ : Subgroup P) (fun x _ y _ => Pcomm x y) p
    let ψ : Ω →* M := φ.comp Ω.subtype
    haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
    haveI : Finite P := Finite.of_equiv (HomC p a n) e.symm.toEquiv
    haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hΩcard : Nat.card Ω ≤ p ^ n := by
      have h1 : Nat.card Ω = Nat.card {x : (⊤ : Subgroup P) // x ^ p = 1} :=
        torsionSubgroup_card (⊤ : Subgroup P) (fun x _ y _ => Pcomm x y) p
      have h2 : Nat.card {x : (⊤ : Subgroup P) // x ^ p = 1} =
          Nat.card {x : HomC p a n // x ^ p = 1} := by
        refine Nat.card_congr
          { toFun := fun x => ⟨e x.1.1, by rw [← map_pow]; rw [show x.1.1 ^ p = 1 from
              congrArg Subtype.val x.2, map_one]⟩
            invFun := fun x => ⟨⟨e.symm x.1, trivial⟩, Subtype.ext (by
              change (e.symm x.1) ^ p = 1
              rw [← map_pow, x.2, map_one])⟩
            left_inv := fun x => by simp
            right_inv := fun x => by simp }
      rw [h1, h2]
      exact homC_card_torsion_le_pow hp
    have hzΩ : z ∈ Ω := (mem_torsionSubgroup _ _ p).2 ⟨trivial, hzp⟩
    have hrange : p ∣ Nat.card ψ.range := by
      have hmem : φ z ∈ ψ.range := ⟨⟨z, hzΩ⟩, rfl⟩
      have h1 : orderOf (⟨φ z, hmem⟩ : ψ.range) ∣ Nat.card ψ.range := orderOf_dvd_natCard _
      rw [← Subgroup.orderOf_coe (⟨φ z, hmem⟩ : ψ.range)] at h1
      rw [← hφz]
      exact h1
    have hmul : Nat.card Ω = Nat.card ψ.range * Nat.card ψ.ker := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h1
      exact h1
    have hle : p ≤ Nat.card ψ.range := Nat.le_of_dvd Nat.card_pos hrange
    let f : {x : φ.ker // x ^ p = 1} → ψ.ker := fun x =>
      ⟨⟨(x.1 : P), (mem_torsionSubgroup _ _ p).2 ⟨trivial, congrArg Subtype.val x.2⟩⟩,
        MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.1.2)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun t : ψ.ker => ((t : Ω) : P)) hxy
      exact this
    have h1 := Nat.card_le_card_of_injective f hf
    have hpn : p ^ n ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos hn
    have h3 : Nat.card ψ.ker * p ≤ p ^ 2 := by
      calc Nat.card ψ.ker * p ≤ Nat.card ψ.ker * Nat.card ψ.range :=
            Nat.mul_le_mul_left _ hle
        _ = Nat.card Ω := by rw [hmul, mul_comm]
        _ ≤ p ^ n := hΩcard
        _ ≤ p ^ 2 := hpn
    have h4 : Nat.card ψ.ker ≤ p := by
      have : Nat.card ψ.ker * p ≤ p * p := by rw [← sq]; exact h3
      exact Nat.le_of_mul_le_mul_right this hp.pos
    exact h1.trans h4
  ·
    intro ha2 x hx hxp
    obtain ⟨y', hy'⟩ := homC_pth_power hp ha2 (e x) (by rw [← map_pow, hxp, map_one])
    set y : P := e.symm y' with hy
    have hyp : y ^ p = x := by
      apply e.injective
      rw [map_pow, hy, MulEquiv.apply_symm_apply, hy']
    have hwp : (φ y) ^ p = 1 := by rw [← map_pow, hyp]; exact MonoidHom.mem_ker.1 hx
    haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
    haveI : Finite P := Finite.of_equiv (HomC p a n) e.symm.toEquiv
    haveI : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    have hC : Nat.card {c : φ.range // c ^ p = 1} ≤ p := by
      classical
      haveI : Fintype φ.range := Fintype.ofFinite _
      have h := IsCyclic.card_pow_eq_one_le (α := φ.range) hp.pos
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact h
    let gz : φ.range := ⟨φ z, z, rfl⟩
    have hgz : orderOf gz = p := by rw [← Subgroup.orderOf_coe gz]; exact hφz
    have hmem : (⟨φ y, y, rfl⟩ : φ.range) ∈ Subgroup.zpowers gz :=
      mem_zpowers_of_card_torsion_le hp hC hgz (Subtype.ext hwp)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : (φ z) ^ k = φ y := congrArg Subtype.val hk
    refine ⟨y * z ^ (-k), ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_zpow, zpow_neg, hk', mul_inv_cancel]
    · rw [(Commute.mul_pow (Pcomm y (z ^ (-k))) p), hyp, ← zpow_natCast, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, hzp, one_zpow, mul_one]

end Kernel

section SylowKer

theorem heis_sylow_ker_data {G C : Type*} [Group G] [Finite G] [Group C] (p : ℕ) [Fact p.Prime]
    {a n : ℕ} (ha : 1 ≤ a) (hG : ∀ P : Sylow p G, Nonempty (↥P ≃* HomC p a n))
    (δ : G →* C) (hcyc : IsCyclic δ.range)
    (hrange : (Nat.card δ.range).factorization p = a) :
    ∀ T : Sylow p δ.ker,
      (∀ x ∈ (T : Subgroup δ.ker), ∀ y ∈ (T : Subgroup δ.ker), x * y = y * x) ∧
      (n ≤ 2 → Nat.card {x : T // x ^ p = 1} ≤ p) ∧
      (2 ≤ a → ∀ x ∈ (T : Subgroup δ.ker), x ^ p = 1 →
        ∃ y ∈ (T : Subgroup δ.ker), y ^ p = x) := by
  intro T
  have hp : p.Prime := Fact.out
  let T' : Subgroup G := (T : Subgroup δ.ker).map δ.ker.subtype
  have hT'p : IsPGroup p T' := T.isPGroup'.map δ.ker.subtype
  obtain ⟨P, hTP⟩ := hT'p.exists_le_sylow
  obtain ⟨e⟩ := hG P
  let φ : ↥(P : Subgroup G) →* C := δ.comp (P : Subgroup G).subtype
  have hkey : ∀ x : G, x ∈ (P : Subgroup G) → δ x = 1 → x ∈ T' := by
    intro x hxP hx
    let Q : Subgroup δ.ker := ((P : Subgroup G) ⊓ δ.ker).subgroupOf δ.ker
    have hQp : IsPGroup p Q :=
      (P.isPGroup'.to_le (inf_le_left : (P : Subgroup G) ⊓ δ.ker ≤ P)).comap_of_injective
        δ.ker.subtype δ.ker.subtype_injective
    have hTQ : (T : Subgroup δ.ker) ≤ Q := by
      intro t ht
      exact ⟨hTP ⟨t, ht, rfl⟩, t.2⟩
    have hQT : Q = (T : Subgroup δ.ker) := T.is_maximal' hQp hTQ
    have hxQ : (⟨x, hx⟩ : δ.ker) ∈ Q := ⟨hxP, hx⟩
    rw [hQT] at hxQ
    exact ⟨⟨x, hx⟩, hxQ, rfl⟩
  let Ψ : (T : Subgroup δ.ker) →* φ.ker :=
    { toFun := fun t => ⟨⟨(t : δ.ker).1, hTP ⟨t, t.2, rfl⟩⟩, by
        have := (t : δ.ker).2
        exact this⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hΨinj : Function.Injective Ψ := by
    intro s t hst
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun y : φ.ker => ((y : ↥(P : Subgroup G)) : G)) hst
    exact this
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    have hy1 : δ ((y : ↥(P : Subgroup G)) : G) = 1 := y.2
    have hyT' := hkey _ (y : ↥(P : Subgroup G)).2 hy1
    obtain ⟨t, htT, ht⟩ := hyT'
    refine ⟨⟨t, htT⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact ht
  let Θ : (T : Subgroup δ.ker) ≃* φ.ker := MulEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩
  haveI : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : Finite δ.range := Finite.of_surjective δ.rangeRestrict δ.rangeRestrict_surjective
  have hcyc' : IsCyclic φ.range := by
    have hle : φ.range ≤ δ.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨(x : G), rfl⟩
    exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hcard : Nat.card φ.range = p ^ a := by
    have hPcard : Nat.card (P : Subgroup G) = p ^ (Nat.card G).factorization p :=
      P.card_eq_multiplicity
    have hTcard : Nat.card (T : Subgroup δ.ker) = p ^ (Nat.card δ.ker).factorization p :=
      T.card_eq_multiplicity
    have h1 : Nat.card (P : Subgroup G) = Nat.card φ.range * Nat.card φ.ker := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h
      exact h
    have h2 : Nat.card φ.ker = Nat.card (T : Subgroup δ.ker) := (Nat.card_congr Θ.toEquiv).symm
    have h3 : Nat.card G = Nat.card δ.ker * Nat.card δ.range := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv] at h
      rw [h, mul_comm]
    have h4 : (Nat.card G).factorization p =
        (Nat.card δ.ker).factorization p + a := by
      rw [h3, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hrange]
    rw [h2, hTcard, hPcard, h4, pow_add] at h1
    have hpos : 0 < p ^ (Nat.card δ.ker).factorization p := pow_pos hp.pos _
    have h5 : Nat.card φ.range * p ^ (Nat.card δ.ker).factorization p =
        p ^ a * p ^ (Nat.card δ.ker).factorization p := by
      rw [← h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h5
  obtain ⟨hab, hn, hpth⟩ := heis_ker_data hp ha e φ hcyc' hcard
  refine ⟨fun x hx y hy => ?_, fun hn2 => ?_, fun ha2 x hx hxp => ?_⟩
  · let x' : (T : Subgroup δ.ker) := ⟨x, hx⟩
    let y' : (T : Subgroup δ.ker) := ⟨y, hy⟩
    have h : x' * y' = y' * x' := by
      apply Θ.injective
      rw [map_mul, map_mul]
      exact Subtype.ext (hab _ (Θ x').2 _ (Θ y').2)
    exact congrArg Subtype.val h
  · have h := hn hn2
    let f : {x : (T : Subgroup δ.ker) // x ^ p = 1} ≃ {x : φ.ker // x ^ p = 1} :=
      { toFun := fun x => ⟨Θ x.1, by rw [← map_pow, x.2, map_one]⟩
        invFun := fun x => ⟨Θ.symm x.1, by rw [← map_pow, x.2, map_one]⟩
        left_inv := fun x => by simp
        right_inv := fun x => by simp }
    exact (le_of_eq (Nat.card_congr f)).trans h
  · let x' : (T : Subgroup δ.ker) := ⟨x, hx⟩
    have hx'p : x' ^ p = 1 := Subtype.ext hxp
    have hΘ : ((Θ x' : φ.ker) : ↥(P : Subgroup G)) ^ p = 1 := by
      have h : (Θ x') ^ p = 1 := by rw [← map_pow, hx'p, map_one]
      exact congrArg Subtype.val h
    obtain ⟨y, hy, hyp⟩ := hpth ha2 (Θ x' : ↥(P : Subgroup G)) (Θ x').2 hΘ
    let y' : φ.ker := ⟨y, hy⟩
    refine ⟨((Θ.symm y' : (T : Subgroup δ.ker)) : δ.ker), (Θ.symm y').2, ?_⟩
    have h : (Θ.symm y') ^ p = x' := by
      apply Θ.injective
      rw [map_pow, MulEquiv.apply_symm_apply]
      exact Subtype.ext hyp
    exact congrArg Subtype.val h

end SylowKer

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
