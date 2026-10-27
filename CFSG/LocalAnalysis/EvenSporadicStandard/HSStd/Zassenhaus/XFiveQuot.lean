module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.XFiveLemma

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open Subgroup CFSG CFSG.EvenSporadicStandard.HSStd CFSG.Blueprint

section Quotient

variable {C : Type} [Group C] (M : Subgroup C) [M.Normal]

@[expose] def quotAut (φ : MulAut C) (hφ : φ * φ = 1) (hM : ∀ m ∈ M, φ m ∈ M) :
    MulAut (C ⧸ M) where
  toFun := QuotientGroup.map M M (φ : C →* C) (fun m hm => hM m hm)
  invFun := QuotientGroup.map M M (φ : C →* C) (fun m hm => hM m hm)
  left_inv x := by
    induction x using QuotientGroup.induction_on with
    | H c =>
      show (QuotientGroup.mk (φ (φ c)) : C ⧸ M) = QuotientGroup.mk c
      have := congrArg (fun ψ : MulAut C => ψ c) hφ
      simp only [MulAut.mul_apply, MulAut.one_apply] at this
      rw [this]
  right_inv x := by
    induction x using QuotientGroup.induction_on with
    | H c =>
      show (QuotientGroup.mk (φ (φ c)) : C ⧸ M) = QuotientGroup.mk c
      have := congrArg (fun ψ : MulAut C => ψ c) hφ
      simp only [MulAut.mul_apply, MulAut.one_apply] at this
      rw [this]
  map_mul' := map_mul _

omit [M.Normal] in
theorem pow_card_succ_eq {m : C} (hm : m ∈ M) : m ^ (Nat.card M + 1) = m := by
  have h : (⟨m, hm⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
  have h2 : m ^ Nat.card M = 1 := congrArg Subtype.val h
  rw [pow_succ, h2, one_mul]

omit [M.Normal] in
theorem eq_one_of_mul_self_eq_one (hodd : Odd (Nat.card M)) {m : C} (hm : m ∈ M)
    (h : m * m = 1) : m = 1 := by
  obtain ⟨j, hj⟩ := hodd
  have h1 := pow_card_succ_eq M hm
  have h2 : m ^ (Nat.card M + 1) = (m * m) ^ (j + 1) := by
    rw [← pow_two, ← pow_mul]; congr 1; omega
  rw [h2, h, one_pow] at h1
  exact h1.symm

omit [M.Normal] in
theorem exists_fixed_of_mk_fixed (hodd : Odd (Nat.card M)) (φ : MulAut C) (hφ : φ * φ = 1)
    {x : C} (hx : (QuotientGroup.mk (φ x) : C ⧸ M) = QuotientGroup.mk x) :
    ∃ n ∈ M, φ (x * n) = x * n := by
  have hφφ : ∀ y : C, φ (φ y) = y := fun y => by
    have := congrArg (fun ψ : MulAut C => ψ y) hφ
    simpa using this
  have hmem : (φ x)⁻¹ * x ∈ M := QuotientGroup.eq.1 hx
  set m : C := x⁻¹ * φ x with hm
  have hmM : m ∈ M := by
    have := M.inv_mem hmem
    simpa [hm] using this
  have hφx : φ x = x * m := by rw [hm]; group
  have hφm : φ m = m⁻¹ := by
    rw [hm, map_mul, map_inv, hφφ]; group
  obtain ⟨j, hj⟩ := hodd
  have hkk : m ^ (j + 1) * m ^ (j + 1) = m := by
    rw [← pow_add]
    have h1 := pow_card_succ_eq M hmM
    have : j + 1 + (j + 1) = Nat.card M + 1 := by omega
    rw [this]; exact h1
  refine ⟨m ^ (j + 1), M.pow_mem hmM _, ?_⟩
  rw [map_mul, hφx, map_pow, hφm, inv_pow]
  have : m * (m ^ (j + 1))⁻¹ = m ^ (j + 1) := by
    rw [mul_inv_eq_iff_eq_mul]; exact hkk.symm
  rw [mul_assoc, this]

omit [M.Normal] in
theorem fixed_of_mk_fixed (hodd : Odd (Nat.card M)) (φ : MulAut C) (hφ : φ * φ = 1)
    (hfix : ∀ m ∈ M, φ m = m)
    {x : C} (hx : (QuotientGroup.mk (φ x) : C ⧸ M) = QuotientGroup.mk x) : φ x = x := by
  have hφφ : ∀ y : C, φ (φ y) = y := fun y => by
    have := congrArg (fun ψ : MulAut C => ψ y) hφ
    simpa using this
  have hmem : (φ x)⁻¹ * x ∈ M := QuotientGroup.eq.1 hx
  set m : C := (φ x)⁻¹ * x with hm
  have h1 : φ m = m⁻¹ := by
    rw [hm, map_mul, map_inv, hφφ]; group
  have h2 : φ m = m := hfix m hmem
  have h3 : m * m = 1 := by
    have : m = m⁻¹ := by rw [← h1, h2]
    calc m * m = m * m⁻¹ := by rw [← this]
      _ = 1 := by group
  have h4 := eq_one_of_mul_self_eq_one M hodd hmem h3
  have : (φ x)⁻¹ * x = 1 := h4
  have h5 := mul_eq_one_iff_eq_inv.1 this
  exact inv_inj.1 h5

end Quotient

section KGroup

variable {G : Type} [Group G]

theorem isKGroupCat_of_kProper_aux [Finite G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {P : Subgroup G} (hP : P ≠ ⊤) : CFSG.SectionRank.IsKGroupCat P :=
  CFSG.KCore.KProperNonab.kGroupAllSimple CFSG.SectionRank.catalog_isoInvariant
    CFSG.SectionRank.catalog_containsAbelianSimple hK P hP

end KGroup

theorem a5_center_trivial :
    ∀ a : alternatingGroup (Fin 5), (∀ b, a * b = b * a) → a = 1 := by decide +kernel

theorem commute_mod_of_X5 (hC : CatE16) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (N : Subgroup G) (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNodd : Odd (Nat.card N))
    (hCtop : centralizer (N : Set G) ≠ ⊤)
    (t : G) (ht2 : t * t = 1) (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (A : Subgroup G) (hA : Nonempty (↥A ≃* alternatingGroup (Fin 5)))
    (hAN : A ≤ centralizer (N : Set G)) (hAt : ∀ a ∈ A, t * a = a * t)
    (hCt : centralizer ({t} : Set G) ⊓ centralizer (N : Set G) ≤ N ⊔ A)
    (u : G) (huA : u ∈ A) (hu : orderOf u = 2)
    (hCu : Nat.card ↥(centralizer ({u} : Set G) ⊓ centralizer (N : Set G)) = 16 * Nat.card N) :
    ∀ a ∈ centralizer ({u} : Set G) ⊓ centralizer (N : Set G),
      ∀ b ∈ centralizer ({u} : Set G) ⊓ centralizer (N : Set G),
        a * b * a⁻¹ * b⁻¹ ∈ N ∧ a * a ∈ N := by
  classical
  set C : Subgroup G := centralizer (N : Set G) with hCdef
  have hcommC : ∀ c ∈ C, ∀ n ∈ N, n * c = c * n := fun c hc n hn => mem_centralizer_iff.1 hc n hn
  have hNC : N ≤ C := fun n hn => mem_centralizer_iff.2 fun h hh => hNab h hh n hn
  set M : Subgroup C := N.subgroupOf C with hMdef
  have hMmem : ∀ c : C, c ∈ M ↔ (c : G) ∈ N := fun c => Subgroup.mem_subgroupOf
  have hMn : M.Normal := ⟨fun n hn g => by
    rw [hMmem] at hn ⊢
    have h1 : (n : G) * g = g * n := hcommC g g.2 n hn
    have : ((g * n * g⁻¹ : C) : G) = n := by
      show (g : G) * n * (g : G)⁻¹ = n
      rw [← h1]; group
    rw [this]; exact hn⟩
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htC : ∀ c ∈ C, MulAut.conj t c ∈ C := by
    intro c hc
    rw [mem_centralizer_iff]
    intro n hn
    have hn' : t⁻¹ * n * t ∈ N := by
      have := htN n hn
      rw [ht1] at this ⊢
      exact this
    have h1 := hcommC c hc _ hn'
    rw [MulAut.conj_apply]
    calc n * (t * c * t⁻¹) = t * ((t⁻¹ * n * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * n * t)) * t⁻¹ := by rw [h1]
      _ = t * c * t⁻¹ * n := by group
  let φ : MulAut C := restrictAut (MulAut.conj t) (conj_mul_self_eq_one ht2) C htC
  have hφval : ∀ c : C, ((φ c : C) : G) = t * c * t⁻¹ := fun c => rfl
  have hφφ' : ∀ c : C, φ (φ c) = c := fun c => by
    apply Subtype.ext
    rw [hφval, hφval, ht1]
    calc t * (t * (c : G) * t) * t = (t * t) * c * (t * t) := by group
      _ = c := by rw [ht2]; group
  have hφφ : φ * φ = 1 := MulEquiv.ext fun c => hφφ' c
  have hMφ : ∀ m ∈ M, φ m ∈ M := by
    intro m hm
    rw [hMmem] at hm ⊢
    rw [hφval]
    exact htN _ hm
  have hMcard : Nat.card M = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
  have hModd : Odd (Nat.card M) := hMcard ▸ hNodd
  let τ : MulAut (↥C ⧸ M) := quotAut M φ hφφ hMφ
  have hττ : τ * τ = 1 := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H c =>
      show (QuotientGroup.mk (φ (φ c)) : ↥C ⧸ M) = QuotientGroup.mk c
      rw [hφφ']
  have hτmk : ∀ c : C, τ (QuotientGroup.mk c) = QuotientGroup.mk (φ c) := fun c => rfl
  let ι : ↥A →* ↥C ⧸ M := (QuotientGroup.mk' M).comp (Subgroup.inclusion hAN)
  have hιval : ∀ a : A, ι a = QuotientGroup.mk (Subgroup.inclusion hAN a) := fun a => rfl
  obtain ⟨eA⟩ := hA
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : (a : G) ∈ N :=
      (hMmem _).1 ((QuotientGroup.eq_one_iff (Subgroup.inclusion hAN a)).1 ha)
    have key : ∀ b : alternatingGroup (Fin 5), eA a * b = b * eA a := by
      intro b
      obtain ⟨b', rfl⟩ := eA.surjective b
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcommC b' (hAN b'.2) a ha')
    have h1 := a5_center_trivial _ key
    exact eA.injective (by rw [h1, map_one])
  have hrange : ι.range = autCentralizer τ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      show τ (ι a) = ι a
      rw [hιval, hτmk]
      congr 1
      apply Subtype.ext
      rw [hφval]
      show t * (a : G) * t⁻¹ = a
      rw [hAt a a.2]; group
    · intro hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have hτy : τ (QuotientGroup.mk y) = QuotientGroup.mk y := hx
      rw [hτmk] at hτy
      obtain ⟨n, hn, hfix⟩ := exists_fixed_of_mk_fixed M hModd φ hφφ hτy
      have hy' : (QuotientGroup.mk (y * n) : ↥C ⧸ M) = QuotientGroup.mk y := by
        rw [QuotientGroup.eq]
        simpa using M.inv_mem (M.inv_mem hn)
      have hfix' : (t : G) * ((y * n : C) : G) * t⁻¹ = ((y * n : C) : G) := by
        have := congrArg Subtype.val hfix
        rwa [hφval] at this
      have hyt : ((y * n : C) : G) ∈ centralizer ({t} : Set G) ⊓ centralizer (N : Set G) := by
        refine ⟨?_, (y * n).2⟩
        show _ ∈ centralizer ({t} : Set G)
        rw [mem_centralizer_singleton_iff]
        calc ((y * n : C) : G) * t = (t * ((y * n : C) : G) * t⁻¹) * t := by rw [hfix']
          _ = t * ((y * n : C) : G) := by group
      obtain ⟨n0, hn0, a0, ha0, hn0a0⟩ := mem_sup_of_commute
        (fun x hx y hy => hcommC y (hAN hy) x hx) (hCt hyt)
      refine ⟨⟨a0, ha0⟩, ?_⟩
      rw [hιval, ← hy', QuotientGroup.eq, hMmem]
      show (a0 : G)⁻¹ * ((y * n : C) : G) ∈ N
      rw [← hn0a0]
      have : (a0 : G)⁻¹ * (n0 * a0) = n0 := by
        have h1 := hcommC a0 (hAN ha0) n0 hn0
        rw [h1]; group
      rw [this]; exact hn0
  let e5 : ↥(autCentralizer τ) ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hι).symm.trans eA)
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu, pow_two] at this
  let uA : A := ⟨u, huA⟩
  let uC : C := ⟨u, hAN huA⟩
  have huC2 : uC * uC = 1 := Subtype.ext hu2
  have hūord : orderOf (ι uA) = 2 := by
    rw [orderOf_injective ι hι uA, Subgroup.orderOf_mk, hu]
  have hū2 : ι uA * ι uA = 1 := by
    rw [← map_mul]
    have : uA * uA = 1 := Subtype.ext hu2
    rw [this, map_one]
  have hū1 : ι uA ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hūord
    omega
  have hūA : ι uA ∈ autCentralizer τ := by
    have : ι uA ∈ ι.range := ⟨uA, rfl⟩
    rwa [hrange] at this
  let H : Subgroup C := (centralizer ({u} : Set G) ⊓ C).subgroupOf C
  have hHmem : ∀ c : C, c ∈ H ↔ (c : G) ∈ centralizer ({u} : Set G) ⊓ C :=
    fun c => Subgroup.mem_subgroupOf
  let f : ↥H →* ↥C ⧸ M := (QuotientGroup.mk' M).comp H.subtype
  have hfM : ∀ m ∈ M, uC * m * uC⁻¹ = m := by
    intro m hm
    rw [hMmem] at hm
    apply Subtype.ext
    have h1 : (m : G) * u = u * m := hcommC uC uC.2 m hm
    show u * (m : G) * u⁻¹ = m
    rw [← h1]; group
  have hfr : f.range = centralizer ({ι uA} : Set (↥C ⧸ M)) := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : ((h : C) : G) * u = u * (h : C) := by
        have : ((h : C) : G) ∈ centralizer ({u} : Set G) := ((hHmem h.1).1 h.2).1
        rwa [mem_centralizer_singleton_iff] at this
      have h2 : (h : C) * uC = uC * h := Subtype.ext h1
      show (QuotientGroup.mk (h : C) : ↥C ⧸ M) * QuotientGroup.mk uC =
        QuotientGroup.mk uC * QuotientGroup.mk (h : C)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h2]
    · intro hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      rw [mem_centralizer_singleton_iff] at hx
      have hx' : (QuotientGroup.mk (MulAut.conj uC y) : ↥C ⧸ M) = QuotientGroup.mk y := by
        rw [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have hx2 : (QuotientGroup.mk y : ↥C ⧸ M) * QuotientGroup.mk uC =
            QuotientGroup.mk uC * QuotientGroup.mk y := hx
        rw [← hx2]; group
      have hy := fixed_of_mk_fixed M hModd (MulAut.conj uC) (conj_mul_self_eq_one huC2)
        (fun m hm => by rw [MulAut.conj_apply]; exact hfM m hm) hx'
      have hy2 := congrArg Subtype.val hy
      rw [MulAut.conj_apply] at hy2
      have hyu : (y : G) * u = u * y := by
        have : (uC * y * uC⁻¹ : C).1 = y := hy2
        have h3 : u * (y : G) * u⁻¹ = y := this
        calc (y : G) * u = (u * (y : G) * u⁻¹) * u := by rw [h3]
          _ = u * y := by group
      refine ⟨⟨y, (hHmem y).2 ⟨?_, y.2⟩⟩, rfl⟩
      show _ ∈ centralizer ({u} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact hyu
  have hker : Nat.card f.ker = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun h => ⟨((h.1 : C) : G), (hMmem _).1
            ((QuotientGroup.eq_one_iff (h.1 : C)).1 (MonoidHom.mem_ker.1 h.2))⟩
        invFun := fun n => ⟨⟨⟨n, hNC n.2⟩, (hHmem _).2 ⟨?_, hNC n.2⟩⟩,
            MonoidHom.mem_ker.2 ((QuotientGroup.eq_one_iff _).2 ((hMmem _).2 n.2))⟩
        left_inv := fun h => rfl
        right_inv := fun n => rfl }
    show (n : G) ∈ centralizer ({u} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact hcommC uC uC.2 n n.2
  have hHcard : Nat.card H = 16 * Nat.card N := by
    rw [← hCu]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      centralizer ({u} : Set G) ⊓ C ≤ C)).toEquiv
  have hTcard : Nat.card (centralizer ({ι uA} : Set (↥C ⧸ M))) = 16 := by
    rw [← hfr]
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hker, hHcard] at h1
    have : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left this (by rw [h1, mul_comm])
  have hτ1 : τ ≠ 1 := by
    intro h1
    have htop : autCentralizer τ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      show τ x = x
      rw [h1]; rfl
    let ψ : ↥C ⧸ M ≃* alternatingGroup (Fin 5) :=
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans e5)
    have := (centralizer_involution_of_equiv_a5 ψ (ι uA) hū1 hū2).1
    omega
  have hX : CFSG.SectionRank.IsKGroupCat (↥C ⧸ M) :=
    (isKGroupCat_of_kProper_aux hKP hCtop).quotient M
  have hmain := elemAbelian_centralizer_of_X5_of_kGroup hC hX τ hττ hτ1 ⟨e5⟩ (ι uA) hūord hūA hTcard
  intro a ha b hb
  have hmemX : ∀ a (ha : a ∈ centralizer ({u} : Set G) ⊓ C),
      (QuotientGroup.mk (⟨a, ha.2⟩ : C) : ↥C ⧸ M) ∈ centralizer ({ι uA} : Set (↥C ⧸ M)) :=
    fun a ha => by
      rw [← hfr]
      exact ⟨⟨⟨a, ha.2⟩, (hHmem _).2 ha⟩, rfl⟩
  have h := hmain _ (hmemX a ha) _ (hmemX b hb)
  refine ⟨?_, ?_⟩
  · have h1 : (QuotientGroup.mk ((⟨a, ha.2⟩ : C) * ⟨b, hb.2⟩ * (⟨a, ha.2⟩ : C)⁻¹ *
        (⟨b, hb.2⟩ : C)⁻¹) : ↥C ⧸ M) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, h.1]
      group
    exact (hMmem _).1 ((QuotientGroup.eq_one_iff _).1 h1)
  · have h1 : (QuotientGroup.mk ((⟨a, ha.2⟩ : C) * ⟨a, ha.2⟩) : ↥C ⧸ M) = 1 := by
      rw [QuotientGroup.mk_mul, h.2]
    exact (hMmem _).1 ((QuotientGroup.eq_one_iff _).1 h1)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
