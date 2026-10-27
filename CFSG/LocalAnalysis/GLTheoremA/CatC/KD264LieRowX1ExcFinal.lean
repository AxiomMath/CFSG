module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie

@[expose] def X1Concl (C₀ : Type) [Group C₀] [Finite C₀] : Prop :=
  ∀ A : Subgroup (MulAut C₀), IsElemAbelian 3 A →
    CFSG.Open.pRank 3 (⊤ : Subgroup C₀) ≤ CFSG.Open.pRank 3 A →
      ∃ F ≤ A, IsElemAbelian 3 F ∧ min 2 (CFSG.Open.pRank 3 A - 1) ≤ CFSG.Open.pRank 3 F ∧
        IsGood 3 F

theorem natCard_quotCenter_eq {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) :=
  Nat.card_congr (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
    (Subgroup.map_center_eq e)).toEquiv

@[expose] noncomputable def jgEquiv {A B : Type*} [Group A] [Group B] (J : Subgroup B)
    (φ : A →* B) (hφ : Function.Injective φ) (hJ : J ≤ φ.range) : ↥(J.comap φ) ≃* ↥J :=
  (Subgroup.equivMapOfInjective (J.comap φ) φ hφ).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hJ))

section Elem

variable {G H : Type*} [Group G] [Group H]

theorem isElemAbelian_map' {p : ℕ} (f : G →* H) {K : Subgroup G} (hK : IsElemAbelian p K) :
    IsElemAbelian p (K.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hK.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_pow, hK.2 x hx, map_one]

theorem isElemAbelian_comap' {p : ℕ} {f : G →* H} (hf : Function.Injective f) {E : Subgroup H}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.comap f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    apply hf
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩)
    simpa using h
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hE.2 _ hx

theorem isElemAbelian_of_le' {p : ℕ} {K E : Subgroup G} (hKE : K ≤ E) (hE : IsElemAbelian p E) :
    IsElemAbelian p K := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (hKE hx)⟩
  apply Subtype.ext
  have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, hKE a.2⟩ ⟨b, hKE b.2⟩)
  simpa using h

theorem isPGroup_of_isElemAbelian' {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) :
    IsPGroup p E := fun g => ⟨1, by
  apply Subtype.ext
  rw [pow_one]
  exact h.2 _ g.2⟩

theorem card_eq_pow_of_isElemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup G} [Finite E]
    (h : IsElemAbelian p E) : ∃ k, Nat.card E = p ^ k := by
  haveI := Fact.mk hp
  exact (isPGroup_of_isElemAbelian' h).exists_card_eq

theorem le_pRank_of_card' [Finite G] {p k : ℕ} (hp : p.Prime) {E H : Subgroup G}
    (hE : IsElemAbelian p E) (hle : E ≤ H) (hcard : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hle, hE, hcard⟩
  rintro k' ⟨E', -, -, hc'⟩
  have h1 : Nat.card E' ≤ Nat.card G := Subgroup.card_le_card_group E'
  rw [hc'] at h1
  have h2 : k' < p ^ k' := Nat.lt_pow_self hp.one_lt
  omega

theorem map_centralizer_conj (g : G) (U : Subgroup G) :
    (Subgroup.centralizer (U : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((U.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hx ⊢
    rintro _ ⟨u, hu, rfl⟩
    have h := hx u hu
    show (MulAut.conj g) u * (MulAut.conj g) x = (MulAut.conj g) x * (MulAut.conj g) u
    rw [← map_mul, ← map_mul, h]
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by show g * (g⁻¹ * y * g) * g⁻¹ = y; group⟩
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hy ⊢
    intro u hu
    have h := hy ((MulAut.conj g) u) ⟨u, hu, rfl⟩
    have h' : g * u * g⁻¹ * y = y * (g * u * g⁻¹) := h
    calc u * (g⁻¹ * y * g) = g⁻¹ * (g * u * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * u * g⁻¹)) * g := by rw [h']
      _ = g⁻¹ * y * g * u := by group

end Elem

section Final

theorem exc_final {C₀ : Type} [Group C₀] [Finite C₀] {G : Type} [Group G]
    (Γ M V U J : Subgroup G) (r : ℕ) (φ : C₀ ≃* Γ)
    (hnorm : ∀ m ∈ M, ∀ x ∈ Γ, m * x * m⁻¹ ∈ Γ)
    (hVΓ : V ≤ Γ) (hVel : IsElemAbelian 3 V) (hVcard : Nat.card V = 3 ^ r)
    (hconj : ∀ E : Subgroup G, E ≤ Γ → IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E →
      ∃ m ∈ M, E.map (MulAut.conj m).toMonoidHom = V)
    (hUV : U ≤ V) (hUcard : Nat.card U = 9)
    (hJ : IsSubnormal J (Γ ⊓ Subgroup.centralizer (U : Set G)))
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJ3 : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    (hinn : ∀ A : Subgroup (MulAut C₀), IsElemAbelian 3 A →
      A ≤ (MulAut.conj : C₀ →* MulAut C₀).range)
    (hinj : Function.Injective (MulAut.conj : C₀ →* MulAut C₀)) :
    X1Concl C₀ := by
  classical
  intro A hA hrank
  set cj : C₀ →* MulAut C₀ := MulAut.conj with hcj
  set f : C₀ →* G := Γ.subtype.comp φ.toMonoidHom with hf
  have hfinj : Function.Injective f := Subtype.val_injective.comp φ.injective
  have hfmem : ∀ c, f c ∈ Γ := fun c => (φ c).2
  have hfrange : f.range = Γ := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact hfmem c
    · intro hx
      obtain ⟨c, hc⟩ := φ.surjective ⟨x, hx⟩
      exact ⟨c, by simp [hf, hc]⟩
  set E : Subgroup C₀ := A.comap cj with hE
  have hEA : E.map cj = A := Subgroup.map_comap_eq_self (hinn A hA)
  have hEel : IsElemAbelian 3 E := isElemAbelian_comap' hinj hA
  have hEcard : Nat.card A = Nat.card E := by
    have := Subgroup.card_map_of_injective (f := cj) hinj (K := E)
    rwa [hEA] at this
  set V₀ : Subgroup C₀ := V.comap f with hV₀
  have hV₀map : V₀.map f = V := by
    rw [hV₀, Subgroup.map_comap_eq, hfrange]
    exact inf_eq_right.2 hVΓ
  have hV₀card : Nat.card V₀ = 3 ^ r := by
    have := Subgroup.card_map_of_injective (f := f) hfinj (K := V₀)
    rw [hV₀map, hVcard] at this
    exact this.symm
  have hV₀el : IsElemAbelian 3 V₀ := isElemAbelian_comap' hfinj hVel
  have hr : r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup C₀) :=
    le_pRank_of_card' Nat.prime_three hV₀el le_top hV₀card
  obtain ⟨kA, hkA⟩ := card_eq_pow_of_isElemAbelian Nat.prime_three hA
  have hpA : CFSG.Open.pRank 3 A = kA :=
    CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card Nat.prime_three hA hkA
  have hrA : r ≤ kA := by rw [← hpA]; exact hr.trans hrank
  have h3r : 3 ^ r ≤ Nat.card E := by
    rw [← hEcard, hkA]
    exact Nat.pow_le_pow_right (by norm_num) hrA
  set EΓ : Subgroup G := E.map f with hEΓ
  have hEΓΓ : EΓ ≤ Γ := by
    rintro _ ⟨c, -, rfl⟩
    exact hfmem c
  have hEΓel : IsElemAbelian 3 EΓ := isElemAbelian_map' f hEel
  have hEΓcard : Nat.card EΓ = Nat.card E := Subgroup.card_map_of_injective hfinj
  obtain ⟨m, hmM, hmV⟩ := hconj EΓ hEΓΓ hEΓel (by rw [hEΓcard]; exact h3r)
  set U' : Subgroup G := U.map (MulAut.conj m⁻¹).toMonoidHom with hU'
  have hU'Γ : U' ≤ Γ := by
    rintro _ ⟨u, hu, rfl⟩
    exact hnorm m⁻¹ (inv_mem hmM) u (hVΓ (hUV hu))
  set F₀ : Subgroup C₀ := U'.comap f with hF₀
  have hF₀map : F₀.map f = U' := by
    rw [hF₀, Subgroup.map_comap_eq, hfrange]
    exact inf_eq_right.2 hU'Γ
  have hU'card : Nat.card U' = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective
  have hF₀card : Nat.card F₀ = 9 := by
    have := Subgroup.card_map_of_injective (f := f) hfinj (K := F₀)
    rw [hF₀map, hU'card, hUcard] at this
    exact this.symm
  have hF₀E : F₀ ≤ E := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := (show f x ∈ U' from hx)
    have hmu : u ∈ EΓ.map (MulAut.conj m).toMonoidHom := hmV ▸ hUV hu
    obtain ⟨e', he', hee'⟩ := hmu
    have h1 : e' = f x := by
      rw [← hux, ← hee']
      show e' = (MulAut.conj m⁻¹) ((MulAut.conj m) e')
      simp only [MulAut.conj_apply]
      group
    rw [h1] at he'
    obtain ⟨e, he, hex⟩ := he'
    have : e = x := hfinj hex
    rw [← this]
    exact he
  have hF₀el : IsElemAbelian 3 F₀ := isElemAbelian_of_le' hF₀E hEel
  set F : Subgroup (MulAut C₀) := F₀.map cj with hF
  have hFA : F ≤ A := hEA ▸ Subgroup.map_mono hF₀E
  have hFel : IsElemAbelian 3 F := isElemAbelian_map' cj hF₀el
  have hFcard : Nat.card F = 3 ^ 2 := by
    rw [hF, Subgroup.card_map_of_injective hinj, hF₀card]
    norm_num
  have hFrank : CFSG.Open.pRank 3 F = 2 :=
    CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card Nat.prime_three hFel hFcard
  refine ⟨F, hFA, hFel, by rw [hFrank]; exact min_le_left _ _, ?_⟩
  set J' : Subgroup G := J.map (MulAut.conj m⁻¹).toMonoidHom with hJ'
  have hΓmap : Γ.map (MulAut.conj m⁻¹).toMonoidHom = Γ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hnorm m⁻¹ (inv_mem hmM) y hy
    · intro hx
      refine ⟨m * x * m⁻¹, hnorm m hmM x hx, ?_⟩
      show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x
      group
  have hJ'sub : IsSubnormal J' (Γ ⊓ Subgroup.centralizer (U' : Set G)) := by
    have h1 := hJ.map (MulAut.conj m⁻¹).toMonoidHom
    have h2 : (Γ ⊓ Subgroup.centralizer (U : Set G)).map (MulAut.conj m⁻¹).toMonoidHom =
        Γ ⊓ Subgroup.centralizer (U' : Set G) := by
      ext y
      constructor
      · rintro ⟨x, ⟨hxΓ, hxC⟩, rfl⟩
        refine ⟨hnorm m⁻¹ (inv_mem hmM) x hxΓ, ?_⟩
        rw [← map_centralizer_conj]
        exact ⟨x, hxC, rfl⟩
      · rintro ⟨hyΓ, hyC⟩
        rw [← map_centralizer_conj] at hyC
        obtain ⟨x, hxC, rfl⟩ := hyC
        refine ⟨x, ⟨?_, hxC⟩, rfl⟩
        have h3 := hnorm m hmM _ hyΓ
        have e : m * ((MulAut.conj m⁻¹).toMonoidHom x) * m⁻¹ = x := by
          show m * (m⁻¹ * x * m⁻¹⁻¹) * m⁻¹ = x
          group
        rwa [e] at h3
    rwa [h2] at h1
  have hJ'Γ : J' ≤ Γ := hJ'sub.le.trans inf_le_left
  set L : Subgroup C₀ := J'.comap f with hL
  have hLsub : IsSubnormal L (⨅ g ∈ F, fixSubgroup g) := by
    rw [hF, iInf_fixSubgroup_conj F₀]
    have h := hJ'sub.comap f
    have h2 : (Γ ⊓ Subgroup.centralizer (U' : Set G)).comap f =
        Subgroup.centralizer (F₀ : Set C₀) := by
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_inf, SetLike.mem_coe,
        Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨-, hx⟩ y hy
        have hyU : f y ∈ U' := hy
        have := hx (f y) hyU
        apply hfinj
        rw [map_mul, map_mul]
        exact this
      · intro hx
        refine ⟨hfmem x, fun u hu => ?_⟩
        obtain ⟨y, hy⟩ : u ∈ f.range := hfrange ▸ hU'Γ hu
        have hyF : y ∈ F₀ := by
          show f y ∈ U'
          rw [hy]
          exact hu
        have := hx y hyF
        rw [← hy]
        have h3 : f (y * x) = f (x * y) := by rw [this]
        rw [map_mul, map_mul] at h3
        exact h3
    rwa [h2] at h
  have hLiso : ↥L ≃* ↥J :=
    (jgEquiv J' f hfinj (hfrange ▸ hJ'Γ)).trans
      (Subgroup.equivMapOfInjective J (MulAut.conj m⁻¹).toMonoidHom
        (MulAut.conj m⁻¹).injective).symm
  have hLq : CFSG.Open.IsQuasisimple ↥L := (CFSG.Open.IsQuasisimple.congr hLiso).2 hJq
  have hLd : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [natCard_quotCenter_eq hLiso]
    exact hJ3
  exact isGood_of_subnormal_quasisimple Nat.prime_three hLsub hLq hLd

end Final

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
