module

public import CFSG.ClassicalInvolution.Q3.TL3DichThmA
public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

namespace CFSG.ClassicalInvolution.Q3.TwistQ

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] {N : Subgroup Y} [N.Normal]

theorem mk_inj {R : Subgroup Y} (hRN : R ⊓ N = ⊥) {a b : Y} (ha : a ∈ R) (hb : b ∈ R)
    (h : QuotientGroup.mk' N a = QuotientGroup.mk' N b) : a = b := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  have hab : a⁻¹ * b ∈ R ⊓ N := ⟨R.mul_mem (R.inv_mem ha) hb, h⟩
  rw [hRN, Subgroup.mem_bot] at hab
  calc a = a * (a⁻¹ * b) := by rw [hab, mul_one]
    _ = b := by group

theorem subgroupMap_injective {R : Subgroup Y} (hRN : R ⊓ N = ⊥) :
    Function.Injective ((QuotientGroup.mk' N).subgroupMap R) := by
  intro a b h
  apply Subtype.ext
  exact mk_inj hRN a.2 b.2 (congrArg Subtype.val h)

theorem centralizer_mk_eq {t : Y} (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1) :
    Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) =
      (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have h1 : QuotientGroup.mk' N (g * t * g⁻¹) = QuotientGroup.mk' N t := by
      rw [map_mul, map_mul, map_inv, hx]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have hn : t⁻¹ * (g * t * g⁻¹) ∈ N := by
      have := N.inv_mem h1
      rwa [show ((g * t * g⁻¹)⁻¹ * t)⁻¹ = t⁻¹ * (g * t * g⁻¹) by group] at this
    have h2 := hnt g _ hn (by group)
    refine ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    have h3 : g * t * g⁻¹ = t := by
      calc g * t * g⁻¹ = t * (t⁻¹ * (g * t * g⁻¹)) := by group
        _ = t := by rw [h2, mul_one]
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h3]
  · rintro ⟨g', hg', hgg⟩
    have hg'' : g' * t = t * g' := Subgroup.mem_centralizer_singleton_iff.mp hg'
    rw [← hgg, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg'']

variable [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [N.Normal] in
theorem inf_eq_bot (hd : TightDatum R S t) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) : R ⊓ N = ⊥ := by
  by_contra h
  exact htN (Subgroup.mem_inf.mp (hd.mem_of_ne_bot inf_le_left (hN2.to_le inf_le_right) h)).2

omit [Finite Y] in
theorem tightCore_map (hRN : R ⊓ N = ⊥) :
    (tightCore R).map (QuotientGroup.mk' N) = tightCore (R.map (QuotientGroup.mk' N)) := by
  unfold tightCore
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hxR, hx2⟩, rfl⟩
    refine ⟨⟨x, hxR, rfl⟩, ?_⟩
    rw [← MonoidHom.map_zpowers]
    exact hx2.map _
  · rintro ⟨⟨x, hxR, rfl⟩, hy2⟩
    refine ⟨x, ⟨hxR, ?_⟩, rfl⟩
    rw [← MonoidHom.map_zpowers] at hy2
    have hxN : Subgroup.zpowers x ⊓ N = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right N (Subgroup.zpowers_le.mpr hxR)).trans hRN.le)
    exact hy2.of_injective _ (subgroupMap_injective hxN)

@[expose] noncomputable def sylowMap (N : Subgroup Y) [N.Normal] (S : Sylow 2 R) :
    Sylow 2 ↥(R.map (QuotientGroup.mk' N)) :=
  S.mapSurjective ((QuotientGroup.mk' N).subgroupMap_surjective R)

theorem coe_sylowMap (S : Sylow 2 R) :
    ((sylowMap N S : Sylow 2 _) : Subgroup ↥(R.map (QuotientGroup.mk' N))) =
      (S : Subgroup R).map ((QuotientGroup.mk' N).subgroupMap R) := rfl

theorem sylowMap_map_subtype (S : Sylow 2 R) :
    ((sylowMap N S : Subgroup _).map (R.map (QuotientGroup.mk' N)).subtype) =
      ((S : Subgroup R).map R.subtype).map (QuotientGroup.mk' N) := by
  rw [coe_sylowMap, Subgroup.map_map, Subgroup.map_map]
  rfl

noncomputable def sylowMapEquiv (hRN : R ⊓ N = ⊥) (S : Sylow 2 R) :
    ↥(S : Subgroup R) ≃* ↥((sylowMap N S : Sylow 2 _) : Subgroup ↥(R.map (QuotientGroup.mk' N))) :=
  Subgroup.equivMapOfInjective (S : Subgroup R) _ (subgroupMap_injective hRN)

noncomputable def mapEquiv (hRN : R ⊓ N = ⊥) : ↥R ≃* ↥(R.map (QuotientGroup.mk' N)) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap R)
    ⟨subgroupMap_injective hRN, (QuotientGroup.mk' N).subgroupMap_surjective R⟩

theorem datum (hd : TightDatum R S t) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1) :
    TightDatum (R.map (QuotientGroup.mk' N)) (sylowMap N S) (QuotientGroup.mk' N t) := by
  have hRN := inf_eq_bot hd hN2 htN
  have hcent : R.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hr)]
  refine ⟨?_, ?_, ?_, hcent, ?_, ?_⟩
  · obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨(sylowMapEquiv hRN S).symm.trans e⟩⟩
  · rw [sylowMap_map_subtype]
    exact Subgroup.mem_map_of_mem _ hd.mem
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hd.order, pow_orderOf_eq_one, map_one]
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htN
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hcent).mpr ?_
    rw [centralizer_mk_eq hnt]
    exact (Subgroup.map_mono hd.le_normalizer).trans (Subgroup.le_normalizer_map _)
  · have he := CFSG.ABGLocalTools.oddCore_map_mulEquiv (mapEquiv (N := N) hRN)
    exact hd.twoGroup.of_equiv (QuotientGroup.congr _ _ (mapEquiv hRN) he)

omit [N.Normal] in
theorem comap_oddCore_le {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (hZc : f.ker ≤ Subgroup.center G) (hZ2 : IsPGroup 2 ↥f.ker) :
    (classicalInvolutionOddCore H).comap f ≤ classicalInvolutionOddCore G ⊔ f.ker := by
  classical
  have : Finite H := Finite.of_surjective f hf
  set M : Subgroup G := (classicalInvolutionOddCore H).comap f with hM
  have hMn : M.Normal := (classicalInvolutionOddCore_normal H).comap f
  have hZM : f.ker ≤ M := fun z hz => by
    show f z ∈ classicalInvolutionOddCore H
    rw [MonoidHom.mem_ker.mp hz]
    exact Subgroup.one_mem _
  set Z' : Subgroup ↥M := f.ker.subgroupOf M with hZ'
  have hZ'2 : IsPGroup 2 ↥Z' := hZ2.comap_subtype
  obtain ⟨P, hZP⟩ := hZ'2.exists_le_sylow
  have hPZ : (P : Subgroup ↥M) ≤ Z' := by
    intro m hm
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have hm2 : IsPGroup 2 ↥(Subgroup.zpowers (f (m : G))) := by
      have e : Subgroup.zpowers (m : G) = (Subgroup.zpowers m).map M.subtype :=
        (MonoidHom.map_zpowers M.subtype m).symm
      rw [← MonoidHom.map_zpowers, e]
      exact ((P.isPGroup'.to_le (Subgroup.zpowers_le.mpr hm)).map _).map _
    exact eq_one_of_isPGroup_of_mem_odd (CFSG.ComponentClassification.OddCore.odd_card H) m.2 hm2
  have hPeq : (P : Subgroup ↥M) = Z' := le_antisymm hPZ hZP
  have hPc : Subgroup.normalizer (P : Set ↥M) ≤ Subgroup.centralizer (P : Set ↥M) := by
    intro m _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : p ∈ Z' := hPeq ▸ hp
    rw [Subgroup.mem_subgroupOf] at hp'
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hZc hp') m).symm
  have hK := MonoidHom.ker_transferSylow_isComplement' P hPc
  have hKodd := MonoidHom.not_dvd_card_ker_transferSylow P hPc
  have hKO : (MonoidHom.transferSylow P hPc).ker ≤ classicalInvolutionOddCore ↥M :=
    le_sSup ⟨MonoidHom.normal_ker _, Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hKodd)⟩
  have hOM : (classicalInvolutionOddCore ↥M).map M.subtype ≤ classicalInvolutionOddCore G := by
    have := hMn
    exact le_sSup ⟨AscThmA.normal_oddCoreOf M, AscThmA.odd_card_oddCoreOf M⟩
  intro m hm
  obtain ⟨⟨k, p⟩, hkp⟩ := hK.2 ⟨m, hm⟩
  have hkp' : (k : G) * (p : G) = m := congrArg Subtype.val hkp
  rw [← hkp']
  refine Subgroup.mul_mem_sup (hOM ⟨k, hKO k.2, rfl⟩) ?_
  have hp : (p : ↥M) ∈ Z' := hPeq ▸ p.2
  exact Subgroup.mem_subgroupOf.mp hp

theorem oddFree (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N)
    (hO : classicalInvolutionOddCore Y = ⊥) : classicalInvolutionOddCore (Y ⧸ N) = ⊥ := by
  have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  have h := comap_oddCore_le (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (by rw [hker]; exact hNc) (by rw [hker]; exact hN2)
  rw [hO, bot_sup_eq, hker] at h
  rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)
    (classicalInvolutionOddCore (Y ⧸ N))]
  exact (Subgroup.map_mono h).trans (le_of_eq ((Subgroup.map_eq_bot_iff _).mpr hker.ge))

omit [Finite Y] in
theorem conjSub_map (g : Y) (H : Subgroup Y) :
    (conjSub g H).map (QuotientGroup.mk' N) =
      conjSub (QuotientGroup.mk' N g) (H.map (QuotientGroup.mk' N)) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem cls (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N)
    (htN : t ∉ N) (hc : TightCls Y R S t) :
    TightCls (Y ⧸ N) (R.map (QuotientGroup.mk' N)) (sylowMap N S) (QuotientGroup.mk' N t) := by
  have hRN := inf_eq_bot hd hN2 htN
  obtain ⟨⟨e⟩, hgen, hO⟩ := hc
  refine ⟨⟨(sylowMapEquiv hRN S).symm.trans e⟩, ?_, oddFree hNc hN2 hO⟩
  have hgen' : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hgen
  show (⨆ g : Y ⧸ N, conjSub g (tightCore (R.map (QuotientGroup.mk' N)))) = ⊤
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← hgen',
    Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [conjSub_map, tightCore_map hRN]
  exact le_iSup (fun g : Y ⧸ N => conjSub g (tightCore (R.map (QuotientGroup.mk' N))))
    (QuotientGroup.mk' N g)

omit [N.Normal] in
theorem card_lt [N.Normal] (hN : N ≠ ⊥) : Nat.card (Y ⧸ N) < Nat.card Y := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN
  have h2 : 0 < Nat.card (Y ⧸ N) := Nat.card_pos
  nlinarith

omit [Finite Y] in
theorem inO2_of (hN2 : IsPGroup 2 ↥N) (h : TightInO2 (QuotientGroup.mk' N t)) : TightInO2 t := by
  obtain ⟨P, hPn, hP2, htP⟩ := h
  refine ⟨P.comap (QuotientGroup.mk' N), hPn.comap _, ?_, htP⟩
  exact hP2.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact hN2)

theorem oddCoreImg_map (hRN : R ⊓ N = ⊥) :
    (oddCoreImg R).map (QuotientGroup.mk' N) = oddCoreImg (R.map (QuotientGroup.mk' N)) := by
  unfold oddCoreImg
  have he := CFSG.ABGLocalTools.oddCore_map_mulEquiv (mapEquiv (N := N) hRN)
  rw [← he, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem mem_oddCoreImg_of_mk (hRN : R ⊓ N = ⊥) {x : Y} (hx : x ∈ R)
    (h : QuotientGroup.mk' N x ∈ oddCoreImg (R.map (QuotientGroup.mk' N))) :
    x ∈ oddCoreImg R := by
  rw [← oddCoreImg_map hRN] at h
  obtain ⟨o, ho, hox⟩ := h
  rwa [← mk_inj hRN (oddCoreImg_le R ho) hx hox]

theorem acts3_map (hd : TightDatum R S t) (hRN : R ⊓ N = ⊥) (h : TightActs3 R t) :
    TightActs3 (R.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t) := by
  obtain ⟨x, k, hxC, hx3, r, hr, hxr⟩ := h
  refine ⟨QuotientGroup.mk' N x, k, ?_, by rw [← map_pow, hx3, map_one],
    QuotientGroup.mk' N r, ⟨r, hr, rfl⟩, fun hmem => hxr ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    rw [← map_mul, ← map_mul, hxC]
  · rw [← map_commutatorElement] at hmem
    have hxr' : ⁅x, r⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hxC) r).mp hr)
        (R.inv_mem hr)
    exact mem_oddCoreImg_of_mk hRN hxr' hmem

omit [Finite Y] in
theorem map_mem_conjClass (hRN : R ⊓ N = ⊥) {K : Subgroup Y}
    (hK : K ∈ CoreAssembly.conjClass (tightCore R)) :
    K.map (QuotientGroup.mk' N) ∈
      CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))) := by
  obtain ⟨g, rfl⟩ := hK
  exact ⟨QuotientGroup.mk' N g, by rw [conjSub_map, tightCore_map hRN]⟩

theorem map_conjSub_ne (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1)
    {g h : Y} (hne : conjSub g (tightCore R) ≠ conjSub h (tightCore R)) :
    (conjSub g (tightCore R)).map (QuotientGroup.mk' N) ≠
      (conjSub h (tightCore R)).map (QuotientGroup.mk' N) := by
  intro heq
  have hRN := inf_eq_bot hd hN2 htN
  have htK : t ∈ tightCore R := hd.isUniqueInvolution_core.mem
  have h1 : QuotientGroup.mk' N (g * t * g⁻¹) ∈
      (conjSub h (tightCore R)).map (QuotientGroup.mk' N) := by
    rw [← heq]
    exact Subgroup.mem_map_of_mem _ (conj_mem_conjSub htK)
  obtain ⟨k, hk, hkg⟩ := h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkg
  set n := k⁻¹ * (g * t * g⁻¹) with hn
  have hgt : g * t * g⁻¹ = k * n := by rw [hn]; group
  have hnZ : ∀ a : Y, a * n = n * a := Subgroup.mem_center_iff.mp (hNc hkg)
  have ht2 : t * t = 1 := t_mul_t hd
  have hk2 : k * k ∈ N := by
    have e1 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    rw [hgt] at e1
    have e2 : (k * n) * (k * n) = (k * k) * (n * n) := by
      calc (k * n) * (k * n) = k * (n * k) * n := by group
        _ = k * (k * n) * n := by rw [← hnZ k]
        _ = (k * k) * (n * n) := by group
    rw [e2] at e1
    have e3 : k * k = (n * n)⁻¹ := eq_inv_of_mul_eq_one_left e1
    rw [e3]
    exact N.inv_mem (N.mul_mem hkg hkg)
  have hkk : k * k = 1 := by
    have hk' := mem_conjSub_iff.mp hk
    have hmemK : h⁻¹ * (k * k) * h ∈ tightCore R := by
      have := (tightCore R).mul_mem hk' hk'
      rwa [show h⁻¹ * k * h * (h⁻¹ * k * h) = h⁻¹ * (k * k) * h by group] at this
    have hmemN : h⁻¹ * (k * k) * h ∈ N := by
      have := (inferInstance : N.Normal).conj_mem _ hk2 h⁻¹
      rwa [inv_inv] at this
    have hbot := Subgroup.mem_inf.mpr ⟨tightCore_le R hmemK, hmemN⟩
    rw [hRN, Subgroup.mem_bot] at hbot
    calc k * k = h * (h⁻¹ * (k * k) * h) * h⁻¹ := by group
      _ = 1 := by rw [hbot]; group
  have hk1 : k ≠ 1 := by
    intro hk1
    rw [hk1, one_mul] at hgt
    apply htN
    have := (inferInstance : N.Normal).conj_mem _ hkg g⁻¹
    rwa [← hgt, inv_inv, show g⁻¹ * (g * t * g⁻¹) * g = t by group] at this
  have hkt : k = h * t * h⁻¹ := by
    rcases (hd.isUniqueInvolution_core.conj h).unique k hk hkk with h' | h'
    · exact absurd h' hk1
    · exact h'
  have hy : (h⁻¹ * g) * t * (h⁻¹ * g)⁻¹ = t * n := by
    calc (h⁻¹ * g) * t * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * t * g⁻¹) * h := by group
      _ = h⁻¹ * (h * t * h⁻¹ * n) * h := by rw [hgt, hkt]
      _ = t * (h⁻¹ * n * h) := by group
      _ = t * n := by rw [mul_assoc h⁻¹, ← hnZ h]; group
  have hn1 : n = 1 := hnt _ _ hkg hy
  apply hne
  have hC : h⁻¹ * g ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [hn1, mul_one] at hy
    calc h⁻¹ * g * t = (h⁻¹ * g) * t * (h⁻¹ * g)⁻¹ * (h⁻¹ * g) := by group
      _ = t * (h⁻¹ * g) := by rw [hy]
  have hfix := conjSub_tightCore_of_mem_normalizer (hd.le_normalizer hC)
  calc conjSub g (tightCore R) = conjSub h (conjSub (h⁻¹ * g) (tightCore R)) := by
        rw [← conjSub_mul]
        congr 1
        group
    _ = conjSub h (tightCore R) := by rw [hfix]

theorem mem_omegaNbr_map (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1)
    {K J : Subgroup Y} (hK : K ∈ CoreAssembly.conjClass (tightCore R))
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) K) :
    J.map (QuotientGroup.mk' N) ∈ omegaNbr
      (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
      (K.map (QuotientGroup.mk' N)) := by
  have hRN := inf_eq_bot hd hN2 htN
  obtain ⟨hJΩ, hJK, P, hP, hPJ, hPN⟩ := hJ
  refine ⟨map_mem_conjClass hRN hJΩ, ?_, P.map (QuotientGroup.mk' N), ?_, Subgroup.map_mono hPJ,
    (Subgroup.map_mono hPN).trans (Subgroup.le_normalizer_map _)⟩
  · obtain ⟨g, rfl⟩ := hJΩ
    obtain ⟨h, rfl⟩ := hK
    exact map_conjSub_ne hd hNc hN2 htN hnt hJK
  · obtain ⟨M, hM, P₀, rfl⟩ := hP
    refine ⟨M.map (QuotientGroup.mk' N), map_mem_conjClass hRN hM,
      P₀.mapSurjective ((QuotientGroup.mk' N).subgroupMap_surjective M), ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    rfl

theorem not_edgeless_map (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1)
    (h : ¬ TightEdgeless R) : ¬ TightEdgeless (R.map (QuotientGroup.mk' N)) := by
  have hRN := inf_eq_bot hd hN2 htN
  intro hE
  apply h
  intro K hK J hJ hKJ
  rcases hKJ with hKJ | hKJ
  · exact hE _ (map_mem_conjClass hRN hK) _ (map_mem_conjClass hRN hJ)
      (Or.inl (mem_omegaNbr_map hd hNc hN2 htN hnt hK hKJ))
  · exact hE _ (map_mem_conjClass hRN hK) _ (map_mem_conjClass hRN hJ)
      (Or.inr (mem_omegaNbr_map hd hNc hN2 htN hnt hJ hKJ))

omit [Finite Y] [N.Normal] in
theorem pow_conj_eq {O : Subgroup Y} {x y o z : Y} (hxO : ∀ u ∈ O, x * u * x⁻¹ ∈ O)
    (ho : o ∈ O) (hz : ∀ a : Y, a * z = z * a) (h : x * y * x⁻¹ * y⁻¹ = o * z) (j : ℕ) :
    ∃ u ∈ O, x ^ j * y * (x ^ j)⁻¹ = u * z ^ j * y := by
  induction j with
  | zero => exact ⟨1, O.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨u, hu, hj⟩ := ih
    refine ⟨x * u * x⁻¹ * o, O.mul_mem (hxO u hu) ho, ?_⟩
    have hxy : x * y * x⁻¹ = o * z * y := by
      calc x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
        _ = o * z * y := by rw [h]
    have hzj : ∀ a : Y, a * z ^ j = z ^ j * a := fun a => (Commute.pow_right (hz a) j)
    calc x ^ (j + 1) * y * (x ^ (j + 1))⁻¹ = x * (x ^ j * y * (x ^ j)⁻¹) * x⁻¹ := by group
      _ = x * (u * z ^ j * y) * x⁻¹ := by rw [hj]
      _ = (x * u * x⁻¹) * (x * z ^ j) * (y * x⁻¹) := by group
      _ = (x * u * x⁻¹) * (z ^ j * x) * (y * x⁻¹) := by rw [hzj x]
      _ = (x * u * x⁻¹) * z ^ j * (x * y * x⁻¹) := by group
      _ = (x * u * x⁻¹) * z ^ j * (o * z * y) := by rw [hxy]
      _ = (x * u * x⁻¹) * (z ^ j * o) * z * y := by group
      _ = (x * u * x⁻¹) * (o * z ^ j) * z * y := by rw [← hzj o]
      _ = (x * u * x⁻¹ * o) * z ^ (j + 1) * y := by rw [pow_succ]; group

omit [N.Normal] in
theorem eq_one_of_comm {O : Subgroup Y} (hOodd : Odd (Nat.card O)) {x y o z : Y} {k : ℕ}
    (hxO : ∀ u ∈ O, x * u * x⁻¹ ∈ O) (hx : x ^ 3 ^ k = 1) (ho : o ∈ O)
    (hz : ∀ a : Y, a * z = z * a) (hz2 : IsPGroup 2 ↥(Subgroup.zpowers z))
    (h : x * y * x⁻¹ * y⁻¹ = o * z) : z = 1 := by
  obtain ⟨u, hu, hj⟩ := pow_conj_eq hxO ho hz h (3 ^ k)
  rw [hx, one_mul, inv_one, mul_one] at hj
  have h1 : u * z ^ 3 ^ k = 1 := by
    calc u * z ^ 3 ^ k = u * z ^ 3 ^ k * y * y⁻¹ := by group
      _ = 1 := by rw [← hj, mul_inv_cancel]
  have h2 : z ^ 3 ^ k ∈ O := by
    rw [eq_inv_of_mul_eq_one_right h1]
    exact O.inv_mem hu
  have h3 : z ^ 3 ^ k = 1 := eq_one_of_isPGroup_of_mem_odd hOodd h2
    (hz2.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _)))
  have h4 : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h3
  obtain ⟨m, hm⟩ := hz2.exists_card_eq
  rw [Nat.card_zpowers] at hm
  rw [hm] at h4
  have hm0 : m = 0 := by
    by_contra hm0
    have h5 : 2 ∣ 3 ^ k := (dvd_pow_self 2 hm0).trans h4
    have h6 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h5
    omega
  rw [hm0, pow_zero] at hm
  exact orderOf_eq_one_iff.mp hm

theorem good_of (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N)
    (htN : t ∉ N) (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1)
    (h : GoodThreeElement (R.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t)) :
    GoodThreeElement R t := by
  classical
  have hRN := inf_eq_bot hd hN2 htN
  have hCbar := centralizer_mk_eq (N := N) hnt
  obtain ⟨xb, k, hxbC, hxb3, ⟨rb, hrb, hxr⟩, hD⟩ := h
  rw [hCbar] at hxbC
  obtain ⟨x, hxC, rfl⟩ := hxbC
  have hxN : x ^ 3 ^ k ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    rw [← map_pow] at hxb3
    exact hxb3
  obtain ⟨n, hnN, hn⟩ : ∃ n ∈ N, n ^ 3 ^ k = (x ^ 3 ^ k)⁻¹ := by
    have hcop : (Nat.card ↥N).Coprime (3 ^ k) := by
      obtain ⟨a, ha⟩ := hN2.exists_card_eq
      rw [ha]
      exact Nat.Coprime.pow _ _ (by norm_num)
    obtain ⟨m, hm⟩ := (powCoprime hcop).surjective ⟨(x ^ 3 ^ k)⁻¹, N.inv_mem hxN⟩
    exact ⟨m, m.2, congrArg Subtype.val hm⟩
  have hnZ : ∀ a : Y, a * n = n * a := Subgroup.mem_center_iff.mp (hNc hnN)
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hNC : N ≤ C := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_center_iff.mp (hNc hm)) t).symm
  set x' := x * n with hx'
  have hx'C : x' ∈ C := C.mul_mem hxC (hNC hnN)
  have hx'3 : x' ^ 3 ^ k = 1 := by
    rw [hx', (show Commute x n from hnZ x).mul_pow, hn, mul_inv_cancel]
  have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hnN
  have hmk : QuotientGroup.mk' N x' = QuotientGroup.mk' N x := by
    rw [hx', map_mul, hn1, mul_one]
  refine ⟨x', k, hx'C, hx'3, ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := hrb
    refine ⟨r, hr, fun hmem => hxr ?_⟩
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hmem
    rwa [oddCoreImg_map hRN, map_commutatorElement, hmk] at h1
  · intro y hyC hyR
    have hyb : QuotientGroup.mk' N y ∈
        Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
      rw [hCbar]
      exact Subgroup.mem_map_of_mem _ hyC
    have hyRb : ∀ rb ∈ R.map (QuotientGroup.mk' N),
        ⁅QuotientGroup.mk' N y, rb⁆ ∈ oddCoreImg (R.map (QuotientGroup.mk' N)) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_commutatorElement, ← oddCoreImg_map hRN]
      exact Subgroup.mem_map_of_mem _ (hyR r hr)
    have hw := hD _ hyb hyRb
    rw [← hmk, ← map_commutatorElement, hCbar] at hw
    have hwC : ⁅x', y⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hx'C hyC) (C.inv_mem hx'C)) (C.inv_mem hyC)
    set f := (QuotientGroup.mk' N).subgroupMap C with hf
    have hfs : Function.Surjective f := (QuotientGroup.mk' N).subgroupMap_surjective C
    have hker : f.ker = N.subgroupOf C := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
    have hkc : f.ker ≤ Subgroup.center ↥C := by
      rw [hker]
      intro c hc
      rw [Subgroup.mem_center_iff]
      intro d
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (hNc (Subgroup.mem_subgroupOf.mp hc))) d)
    have hk2 : IsPGroup 2 ↥f.ker := by
      rw [hker]
      exact hN2.comap_subtype
    have hle := comap_oddCore_le f hfs hkc hk2
    obtain ⟨u, hu, hwu⟩ := hw
    have hwmem : (⟨⁅x', y⁆, hwC⟩ : ↥C) ∈
        (classicalInvolutionOddCore ↥(C.map (QuotientGroup.mk' N))).comap f := by
      rw [Subgroup.mem_comap]
      have e : f ⟨_, hwC⟩ = u := Subtype.ext hwu.symm
      rw [e]
      exact hu
    have hw2 := hle hwmem
    rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hw2
    obtain ⟨o, ho, z, hz, hoz⟩ := hw2
    have hzN : (z : Y) ∈ N := by
      rw [hker] at hz
      exact Subgroup.mem_subgroupOf.mp hz
    have hoz' : x' * y * x'⁻¹ * y⁻¹ = (o : Y) * (z : Y) := by
      rw [← commutatorElement_def]
      exact (congrArg Subtype.val hoz).symm
    have hoO : (o : Y) ∈ oddCoreImg C := ⟨o, ho, rfl⟩
    have hxO : ∀ u ∈ oddCoreImg C, x' * u * x'⁻¹ ∈ oddCoreImg C := fun u hu =>
      conj_mem_oddCoreImg (Subgroup.le_normalizer hx'C) hu
    have hz1 : (z : Y) = 1 := eq_one_of_comm (odd_natCard_oddCoreImg C) hxO hx'3 hoO
      (Subgroup.mem_center_iff.mp (hNc hzN)) (hN2.to_le (Subgroup.zpowers_le.mpr hzN)) hoz'
    rw [commutatorElement_def, hoz', hz1, mul_one]
    exact hoO

end CFSG.ClassicalInvolution.Q3.TwistQ
