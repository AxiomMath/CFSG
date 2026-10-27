module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalSplitAbelian
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Layer

section Generic

theorem natCard_comap_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (N : Subgroup H) :
    Nat.card ↥(N.comap f) = Nat.card ↥f.ker * Nat.card ↥N := by
  have : Finite H := Finite.of_surjective f hf
  have h1 := (N.comap f).card_mul_index
  have h2 := N.card_mul_index
  have h3 : (N.comap f).index = N.index := Subgroup.index_comap_of_surjective N hf
  have h4 : Nat.card G = Nat.card H * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  rw [h3] at h1
  have h5 : Nat.card ↥(N.comap f) * N.index = Nat.card ↥f.ker * Nat.card ↥N * N.index := by
    rw [h1, h4, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h5

theorem isPGroup_comap_of_surjective {p : ℕ} [Fact p.Prime] {G H : Type*} [Group G] [Group H]
    [Finite G] (f : G →* H) (hf : Function.Surjective f) {N : Subgroup H}
    (hker : IsPGroup p ↥f.ker) (hN : IsPGroup p ↥N) : IsPGroup p ↥(N.comap f) := by
  have : Finite H := Finite.of_surjective f hf
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hker
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hN
  exact IsPGroup.iff_card.2 ⟨a + b, by rw [natCard_comap_of_surjective f hf, ha, hb, pow_add]⟩

theorem not_dvd_natCard_of_exponent_dvd {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q]
    [Finite Q] (hexp : Monoid.exponent Q ∣ p - 1) : ¬ p ∣ Nat.card Q := by
  intro hdvd
  have : Fintype Q := Fintype.ofFinite Q
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := Q) p
    (by simpa [Nat.card_eq_fintype_card] using hdvd)
  have h0 : orderOf x ∣ p - 1 := (Monoid.order_dvd_exponent x).trans hexp
  rw [hx] at h0
  exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.out.one_lt)
    (Nat.sub_lt hp.out.pos one_pos) h0

theorem pPrimeCore_quotient_eq_bot {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G] :
    CFSG.pPrimeCore p (G ⧸ CFSG.pPrimeCore p G) = ⊥ := by
  classical
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  let π := QuotientGroup.mk' (CFSG.pPrimeCore p G)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hM : (N.comap π).Normal := hN.comap π
  have hMcop : Nat.Coprime p (Nat.card ↥(N.comap π)) := by
    have hker : π.ker = CFSG.pPrimeCore p G := QuotientGroup.ker_mk' _
    rw [natCard_comap_of_surjective π hπ, hker]
    exact Nat.Coprime.mul_right CFSG.pPrimeCore_coprime_card hcop
  have hle : N.comap π ≤ CFSG.pPrimeCore p G := by
    unfold CFSG.pPrimeCore
    exact le_sSup ⟨hM, hMcop⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := hπ x
  have := hle (show g ∈ N.comap π from hx)
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff g).2 this

theorem nilpotent_of_le_frattini {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (h : K ≤ frattini G) : Group.IsNilpotent ↥K := by
  have : Group.IsNilpotent ↥(frattini G) := frattini_nilpotent
  have h1 : Group.IsNilpotent ↥(K.subgroupOf (frattini G)) := inferInstance
  exact Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe h).surjective

theorem le_frattini_of_forall_coatom {G : Type*} [Group G] (K : Subgroup G)
    (h : ∀ M : Subgroup G, IsCoatom M → K ≤ M) : K ≤ frattini G := by
  show K ≤ Order.radical (Subgroup G)
  unfold Order.radical
  exact le_iInf₂ fun M hM => h M hM

end Generic

section Core

variable {p : ℕ} [hp : Fact p.Prime] {Y S Q : Type*} [Group Y] [Finite Y] [Group S] [Group Q]

theorem rank_bound_core (θ : Y →* S) (hθ : Function.Surjective θ) (hkerθ : IsPGroup p ↥θ.ker)
    (π : S →* Q) (hπ : Function.Surjective π) (hQc : ∀ x y : Q, x * y = y * x)
    (hexp : Monoid.exponent Q ∣ p - 1) (hN : IsPGroup p ↥π.ker)
    (hC : ∀ s : S, (∀ n ∈ π.ker, s * n = n * s) → s ∈ π.ker) :
    ∀ q : ℕ, q.Prime → q ∣ p - 1 → ∀ Q₀ : Subgroup Q, CFSG.IsElementaryAbelian q Q₀ →
      Nat.card Q₀ ≤ q ^ CFSG.pRank p Y := by
  classical
  have : Finite S := Finite.of_surjective θ hθ
  have : Finite Q := Finite.of_surjective π hπ
  let Θ : Y →* Q := π.comp θ
  have hΘ : Function.Surjective Θ := hπ.comp hθ
  let R : Subgroup Y := Θ.ker
  have hRn : R.Normal := MonoidHom.normal_ker Θ
  have hR : R = π.ker.comap θ := (MonoidHom.comap_ker π θ).symm
  have hRp : IsPGroup p ↥R := by rw [hR]; exact isPGroup_comap_of_surjective θ hθ hkerθ hN
  have hQp : ¬ p ∣ Nat.card Q := not_dvd_natCard_of_exponent_dvd hexp
  have hidx : R.index = Nat.card Q := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hΘ, Subgroup.card_top]
  have hcop : Nat.Coprime (Nat.card ↥R) R.index := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hRp
    rw [ha, hidx]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hQp)
  obtain ⟨C, hCcomp⟩ := Subgroup.exists_right_complement'_of_coprime (N := R) hcop
  have hdisj : Disjoint R C := hCcomp.disjoint
  have hCcard : Nat.card ↥R * Nat.card ↥C = Nat.card Y := hCcomp.card_mul_card
  have hinj : Function.Injective (Θ.comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have h1 : (c : Y) ∈ R := hc
    have h2 : (c : Y) ∈ C := c.2
    have h3 : (c : Y) ∈ R ⊓ C := ⟨h1, h2⟩
    rw [disjoint_iff.1 hdisj, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.2 (Subtype.ext h3)
  have hcardC : Nat.card ↥C = Nat.card Q := by
    have h1 := R.card_mul_index
    rw [hidx] at h1
    have hRpos : 0 < Nat.card ↥R := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hRpos (hCcard.trans h1.symm)
  have hsurj : Function.Surjective (Θ.comp C.subtype) :=
    (Function.Injective.bijective_of_nat_card_le hinj (le_of_eq hcardC.symm)).2
  let eC : ↥C ≃* Q := MulEquiv.ofBijective (Θ.comp C.subtype) ⟨hinj, hsurj⟩
  let ψ : ↥C →* MulAut ↥R := MulAut.conjNormal.comp C.subtype
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcent : ∀ r : ↥R, (c : Y) * r * (c : Y)⁻¹ = r := fun r => by
      have := congrArg (fun φ : MulAut ↥R => ((φ r : ↥R) : Y)) hc
      simpa [ψ, MulAut.conjNormal_apply] using this
    have hθc : ∀ n ∈ π.ker, θ (c : Y) * n = n * θ (c : Y) := by
      intro n hn
      obtain ⟨y, rfl⟩ := hθ n
      have hy : y ∈ R := by
        show Θ y = 1
        exact hn
      have := hcent ⟨y, hy⟩
      have h1 : (c : Y) * y = y * (c : Y) := by
        have h2 := congrArg (fun z : Y => z * (c : Y)) this
        simpa [mul_assoc] using h2
      rw [← map_mul, ← map_mul, h1]
    have hcπ : (c : Y) ∈ R := by
      show Θ (c : Y) = 1
      exact hC _ hθc
    have h3 : (c : Y) ∈ R ⊓ C := ⟨hcπ, c.2⟩
    rw [disjoint_iff.1 hdisj, Subgroup.mem_bot] at h3
    exact Subgroup.mem_bot.2 (Subtype.ext h3)
  let Ĉ : Subgroup (MulAut ↥R) := ψ.range
  have hCcomm : ∀ c d : ↥C, c * d = d * c := fun c d => by
    apply eC.injective
    rw [map_mul, map_mul, hQc]
  have hĈc : IsMulCommutative Ĉ := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    show (a : MulAut ↥R) * b = b * a
    rw [← hc, ← hd, ← map_mul, ← map_mul, hCcomm]
  have hĈexp : Monoid.exponent ↥Ĉ ∣ p - 1 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 a.2
    apply Subtype.ext
    show ((a : MulAut ↥R)) ^ (p - 1) = 1
    rw [← hc, ← map_pow]
    have : c ^ (p - 1) = 1 := by
      apply eC.injective
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hexp _
    rw [this, map_one]
  obtain ⟨D, -, -, -, -, E, r, -, -, -, -, hm⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.split_abelian_coprime_automorphism_rank_bound
      hRp Ĉ hĈc hĈexp
  have hbound : ∀ X : Subgroup ↥R, CFSG.IsElementaryAbelian p X →
      Nat.card X ≤ p ^ CFSG.pRank p Y := by
    intro X hX
    let X' : Subgroup Y := X.map R.subtype
    have hXX' : ↥X ≃* ↥X' := X.equivMapOfInjective R.subtype R.subtype_injective
    have hX' : CFSG.IsElementaryAbelian p X' := isElementaryAbelian_of_equiv hXX'.symm hX
    have hXp : IsPGroup p ↥X := CFSG.IsElementaryAbelian.isPGroup p ↥X
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hXp
    have hk' : Nat.card X' = p ^ k := by rw [← Nat.card_congr hXX'.toEquiv, hk]
    have hkle : k ≤ CFSG.pRank p Y := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.SectionRank.le_pRank hp.out.one_lt le_top
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p X').1 hX') hk'
    rw [hk]
    exact Nat.pow_le_pow_right hp.out.pos hkle
  obtain ⟨-, hrank, -⟩ := hm (CFSG.pRank p Y) hbound
  intro q hq hqp Q₀ hQ₀
  let f : Q →* MulAut ↥R := ψ.comp eC.symm.toMonoidHom
  have hf : Function.Injective f := hψ.comp eC.symm.injective
  have hfle : Q₀.map f ≤ Ĉ := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨eC.symm x, rfl⟩
  have hQ₀f : CFSG.IsElementaryAbelian q (Q₀.map f) :=
    isElementaryAbelian_of_equiv (Q₀.equivMapOfInjective f hf).symm hQ₀
  have hfinal := hrank q hq hqp (Q₀.map f) hfle hQ₀f
  rwa [Subgroup.card_map_of_injective hf] at hfinal

end Core

section Reduction

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G] {S Q : Type*} [Group S]
  [Group Q]

theorem sectionRankBound (Y₀ : Subgroup G) (θ : ↥Y₀ →* S) (hθ : Function.Surjective θ)
    (π : S →* Q) (hπ : Function.Surjective π) (hQc : ∀ x y : Q, x * y = y * x)
    (hexp : Monoid.exponent Q ∣ p - 1) (hN : IsPGroup p ↥π.ker)
    (hC : ∀ s : S, (∀ n ∈ π.ker, s * n = n * s) → s ∈ π.ker) :
    ∀ q : ℕ, q.Prime → q ∣ p - 1 → ∀ Q₀ : Subgroup Q, CFSG.IsElementaryAbelian q Q₀ →
      Nat.card Q₀ ≤ q ^ CFSG.pRank p G := by
  classical
  have : Finite S := Finite.of_surjective θ hθ
  obtain ⟨Y, hY, hYmin⟩ := (wellFounded_lt (α := Subgroup ↥Y₀)).has_min
    {Y | Y.map θ = ⊤}
    ⟨⊤, show Subgroup.map θ ⊤ = ⊤ by rw [Subgroup.map_top, MonoidHom.range_eq_top.2 hθ]⟩
  let θY : ↥Y →* S := θ.comp Y.subtype
  have hθY : Function.Surjective θY := by
    intro s
    have : s ∈ Y.map θ := by rw [show Y.map θ = ⊤ from hY]; trivial
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  let K : Subgroup ↥Y := θY.ker
  have hKn : K.Normal := MonoidHom.normal_ker θY
  have hKfr : K ≤ frattini ↥Y := by
    refine le_frattini_of_forall_coatom K fun M hM => ?_
    by_contra hKM
    have hsup : M ⊔ K = ⊤ :=
      hM.2 (M ⊔ K) (lt_of_le_of_ne le_sup_left fun h => hKM (le_sup_right.trans h.symm.le))
    have hMtop : M.map θY = ⊤ := by
      rw [eq_top_iff]
      intro s _
      obtain ⟨z, rfl⟩ := hθY s
      have hz : z ∈ K ⊔ M := by rw [sup_comm, hsup]; trivial
      obtain ⟨k, hk, m, hm, rfl⟩ := mem_sup_mul (A := M) (L := K)
        (by rw [Subgroup.normalizer_eq_top_iff.2 hKn]; exact le_top) hz
      refine ⟨m, hm, ?_⟩
      rw [map_mul, show θY k = 1 from hk, one_mul]
    have hM' : (M.map Y.subtype).map θ = ⊤ := by
      rw [Subgroup.map_map]; exact hMtop
    refine hYmin _ hM' (lt_of_le_of_ne (Subgroup.map_subtype_le M) fun heq => hM.1 ?_)
    rw [eq_top_iff]
    intro y _
    have hy : (y : ↥Y₀) ∈ M.map Y.subtype := by rw [heq]; exact y.2
    obtain ⟨m, hm, hmy⟩ := hy
    have : m = y := Subtype.ext hmy
    rw [← this]; exact hm
  have hKnil : Group.IsNilpotent ↥K := nilpotent_of_le_frattini K hKfr
  let J : Subgroup ↥Y := CFSG.pPrimeCore p ↥Y
  have hJcop : ¬ p ∣ Nat.card ↥J :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).1 CFSG.pPrimeCore_coprime_card
  have hJK : J ≤ K := by
    let N₁ : Subgroup S := J.map θY
    have hN₁n : N₁.Normal := (inferInstance : J.Normal).map θY hθY
    have hN₁cop : ¬ p ∣ Nat.card ↥N₁ := fun h => hJcop (h.trans (Subgroup.card_map_dvd J θY))
    have hinter : ∀ x ∈ N₁, x ∈ π.ker → x = 1 := by
      intro x hx1 hx2
      obtain ⟨k, hk⟩ := hN ⟨x, hx2⟩
      have h1 : orderOf x ∣ Nat.card ↥N₁ := Subgroup.orderOf_dvd_natCard N₁ hx1
      have h2 : orderOf x ∣ p ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        exact congrArg Subtype.val hk
      have hc : Nat.Coprime (p ^ k) (Nat.card ↥N₁) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN₁cop)
      have h3 : Nat.Coprime (orderOf x) (orderOf x) :=
        (hc.coprime_dvd_left h2).coprime_dvd_right h1
      exact orderOf_eq_one_iff.1 (Nat.coprime_self _ |>.1 h3)
    have hcomm : ∀ n ∈ N₁, ∀ m ∈ π.ker, n * m = m * n := by
      intro n hn m hm
      have hmn : m * n⁻¹ * m⁻¹ ∈ N₁ := hN₁n.conj_mem _ (N₁.inv_mem hn) m
      have h1 : n * m * n⁻¹ * m⁻¹ ∈ N₁ := by
        have := N₁.mul_mem hn hmn
        simpa [mul_assoc] using this
      have hker : π.ker.Normal := MonoidHom.normal_ker π
      have h2 : n * m * n⁻¹ * m⁻¹ ∈ π.ker := by
        have := π.ker.mul_mem (hker.conj_mem m hm n) (π.ker.inv_mem hm)
        simpa [mul_assoc] using this
      have h3 : n * m * n⁻¹ * m⁻¹ = 1 := hinter _ h1 h2
      exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)
    intro j hj
    have hjN : θY j ∈ N₁ := ⟨j, hj, rfl⟩
    have hjker : θY j ∈ π.ker := hC _ fun m hm => hcomm _ hjN m hm
    exact hinter _ hjN hjker
  let θbar : (↥Y ⧸ J) →* S := QuotientGroup.lift J θY (fun j hj => hJK hj)
  have hθbar : Function.Surjective θbar := fun s => by
    obtain ⟨y, rfl⟩ := hθY s
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hkerbar : IsPGroup p ↥θbar.ker := by
    have hmem : ∀ x : ↥K, θbar (QuotientGroup.mk (x : ↥Y)) = 1 := fun x => x.2
    let g : ↥K →* ↥θbar.ker :=
      ((QuotientGroup.mk' J).comp K.subtype).codRestrict θbar.ker fun x => hmem x
    have hg : Function.Surjective g := by
      intro z
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (z : ↥Y ⧸ J)
      have hyK : y ∈ K := by
        have : θbar (QuotientGroup.mk y) = 1 := by rw [hy]; exact z.2
        exact this
      exact ⟨⟨y, hyK⟩, Subtype.ext hy⟩
    have hnil : Group.IsNilpotent ↥θbar.ker := Group.nilpotent_of_surjective g hg
    exact CFSG.isPGroup_of_nilpotent_normal θbar.ker (MonoidHom.normal_ker θbar) hnil
      pPrimeCore_quotient_eq_bot
  have hrank : CFSG.pRank p (↥Y ⧸ J) ≤ CFSG.pRank p G := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp.out J hJcop,
      CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_le_of_injective hp.out.one_lt (Y₀.subtype.comp Y.subtype)
      (Subtype.val_injective.comp Subtype.val_injective)
  intro q hq hqp Q₀ hQ₀
  exact (rank_bound_core θbar hθbar hkerbar π hπ hQc hexp hN hC q hq hqp Q₀ hQ₀).trans
    (Nat.pow_le_pow_right hq.pos hrank)

end Reduction

section Main

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G] {B : Type*} [Group B]

theorem sym_three_pow_section_forces_three_rank (s : ℕ) (Y₀ : Subgroup G)
    (f : ↥Y₀ →* (Fin s → Equiv.Perm (Fin 3))) (hf : Function.Surjective f) :
    s ≤ CFSG.pRank 3 G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : (Fin s → Equiv.Perm (Fin 3)) →* (Fin s → ℤˣ) :=
    MonoidHom.pi fun i => Equiv.Perm.sign.comp (Pi.evalMonoidHom (fun _ => Equiv.Perm (Fin 3)) i)
  have hπapp : ∀ σ i, π σ i = Equiv.Perm.sign (σ i) := fun σ i => rfl
  have hπ : Function.Surjective π := by
    intro u
    refine ⟨fun i => if u i = 1 then 1 else Equiv.swap 0 1, funext fun i => ?_⟩
    rw [hπapp]
    by_cases h : u i = 1
    · simp [h]
    · have : u i = -1 := (Int.units_eq_one_or (u i)).resolve_left h
      simp [this, Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 1 by decide)]
  have hQc : ∀ x y : Fin s → ℤˣ, x * y = y * x := fun x y => mul_comm x y
  have hexp : Monoid.exponent (Fin s → ℤˣ) ∣ 3 - 1 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => funext fun i => ?_
    exact Int.units_sq (g i)
  have hN : IsPGroup 3 ↥π.ker := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    funext i
    have hx : Equiv.Perm.sign ((x : Fin s → Equiv.Perm (Fin 3)) i) = 1 := by
      have := congrFun x.2 i
      simpa [hπapp] using this
    have h3 := (by decide : ∀ τ : Equiv.Perm (Fin 3), Equiv.Perm.sign τ = 1 → τ ^ 3 = 1) _ hx
    simpa using h3
  have hC : ∀ σ : Fin s → Equiv.Perm (Fin 3), (∀ n ∈ π.ker, σ * n = n * σ) → σ ∈ π.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    funext i
    rw [hπapp]
    let n : Fin s → Equiv.Perm (Fin 3) := Pi.mulSingle i (finRotate 3)
    have hn : n ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      funext j
      rw [hπapp]
      by_cases hji : j = i
      · subst hji
        simp [n]
      · simp [n, Pi.mulSingle_eq_of_ne hji]
    have h := congrFun (hσ n hn) i
    simp only [Pi.mul_apply, n, Pi.mulSingle_eq_same] at h
    exact (by decide : ∀ τ : Equiv.Perm (Fin 3), τ * finRotate 3 = finRotate 3 * τ →
      Equiv.Perm.sign τ = 1) _ h
  have hT : CFSG.IsElementaryAbelian 2 (Fin s → ℤˣ) :=
    { is_comm := ⟨fun a b => mul_comm a b⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        funext fun i => Int.units_sq (g i) }
  have hTop : CFSG.IsElementaryAbelian 2 (⊤ : Subgroup (Fin s → ℤˣ)) :=
    isElementaryAbelian_of_equiv Subgroup.topEquiv hT
  have key := sectionRankBound (p := 3) Y₀ f hf π hπ hQc hexp hN hC 2 Nat.prime_two
    (by norm_num) ⊤ hTop
  have hcard : Nat.card (⊤ : Subgroup (Fin s → ℤˣ)) = 2 ^ s := by
    rw [Subgroup.card_top, Nat.card_pi]
    have : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
    simp
  rw [hcard] at key
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 key

end Main

end CFSG.QuasithinUnique.Setup.Lift
