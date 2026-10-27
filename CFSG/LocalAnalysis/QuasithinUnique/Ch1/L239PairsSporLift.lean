
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Lift
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsCases

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def GoodLocal {X : Type*} [Group X] (Kx : Subgroup X) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (φ : ↥K →* ↥Kx), Function.Surjective φ →
    IsPGroup 2 φ.ker → CharTwo K ∧ ¬ HasChi0Block K

theorem GoodLocal.map {X X' : Type*} [Group X] [Group X'] {Kx : Subgroup X} (h : GoodLocal Kx)
    (f : X ≃* X') : GoodLocal (Kx.map f.toMonoidHom) := by
  intro G _ _ K φ hφ hker
  let e : ↥Kx ≃* ↥(Kx.map f.toMonoidHom) := Kx.equivMapOfInjective f.toMonoidHom f.injective
  refine h G K (e.symm.toMonoidHom.comp φ) (e.symm.surjective.comp hφ) ?_
  have : (e.symm.toMonoidHom.comp φ).ker = φ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff e.symm e.symm.injective
  rwa [this]

theorem GoodLocal.of_data {X : Type*} [Group X] {Kx : Subgroup X} [Finite ↥Kx]
    (Q : Subgroup ↥Kx) [Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hcent : ∀ y : ↥Kx, (∀ q ∈ Q, y * q = q * y) → y ∈ Q)
    (hA3 : ∀ b : ↥Kx, orderOf b = 3 → 4 < Nat.card ↥⁅Q, Subgroup.zpowers b⁆)
    (hN : ∀ n : ℕ, 2 ≤ n → ¬ (2 ^ n * (4 ^ n - 1) ∣ Nat.card (↥Kx ⧸ Q))) : GoodLocal Kx := by
  intro G _ _ K φ hφ hker
  exact charTwo_noChi0_of_quotient φ hφ hker Q hQ2 hcent hA3 hN

section Induced

theorem exists_induced_mulAut {L X : Type*} [Group L] [Group X] (θ : L →* X)
    (hθ : Function.Surjective θ) (c : MulAut L) (hc : θ.ker.comap c.toMonoidHom = θ.ker) :
    ∃ cbar : MulAut X, ∀ l, cbar (θ l) = θ (c l) := by
  have hc' : θ.ker.comap c.symm.toMonoidHom = θ.ker := by
    ext l
    have h1 : l ∈ θ.ker.comap c.symm.toMonoidHom ↔ c.symm l ∈ θ.ker := Iff.rfl
    rw [h1]
    constructor
    · intro h
      have : c (c.symm l) ∈ θ.ker := by
        have h2 : c.symm l ∈ θ.ker.comap c.toMonoidHom := by rw [hc]; exact h
        exact h2
      simpa using this
    · intro h
      have h2 : c.symm l ∈ θ.ker.comap c.toMonoidHom := by
        show c (c.symm l) ∈ θ.ker
        simpa using h
      rwa [hc] at h2
  have hle : θ.ker ≤ (θ.comp c.toMonoidHom).ker := by
    intro l hl
    have : l ∈ θ.ker.comap c.toMonoidHom := by rw [hc]; exact hl
    exact this
  have hle' : θ.ker ≤ (θ.comp c.symm.toMonoidHom).ker := by
    intro l hl
    have : l ∈ θ.ker.comap c.symm.toMonoidHom := by rw [hc']; exact hl
    exact this
  let g : X →* X := (θ.liftOfSurjective hθ) ⟨θ.comp c.toMonoidHom, hle⟩
  let g' : X →* X := (θ.liftOfSurjective hθ) ⟨θ.comp c.symm.toMonoidHom, hle'⟩
  have hg : ∀ l, g (θ l) = θ (c l) := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply θ _ _ ⟨θ.comp c.toMonoidHom, hle⟩ l
  have hg' : ∀ l, g' (θ l) = θ (c.symm l) := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply θ _ _ ⟨θ.comp c.symm.toMonoidHom, hle'⟩ l
  refine ⟨MulEquiv.mk' ⟨g, g', ?_, ?_⟩ (fun x y => map_mul g x y), fun l => hg l⟩
  · intro y
    obtain ⟨l, rfl⟩ := hθ y
    simp [hg, hg']
  · intro y
    obtain ⟨l, rfl⟩ := hθ y
    simp [hg, hg']

end Induced

theorem pairConclusion_of_local_pair {G : Type} [Group G] [Finite G] {L R : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylowTwoOf (R ⊓ L) L)
    {X : Type} [Group X] [Finite X] (θ0 : ↥L →* X) (hθ0 : Function.Surjective θ0)
    (hker : θ0.ker = CFSG.pCore 2 ↥L) (S₀ : Subgroup X) (hS₀ : IsPGroup 2 S₀)
    (hS₀i : ¬ 2 ∣ S₀.index) (K₁ K₂ : Subgroup X)
    (hinv₁ : ∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ → K₁.map α.toMonoidHom = K₁)
    (hinv₂ : ∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ → K₂.map α.toMonoidHom = K₂)
    (hne₁ : K₁ ≠ ⊤) (hne₂ : K₂ ≠ ⊤) (hsup : K₁ ⊔ K₂ = ⊤) (hg₁ : GoodLocal K₁)
    (hg₂ : GoodLocal K₂) : PairConclusion L R := by
  classical
  have hNker2 : IsPGroup 2 θ0.ker := by rw [hker]; exact CFSG.pCore_isPGroup
  set SL : Subgroup ↥L := (R ⊓ L).subgroupOf L with hSL
  have hSL2 : IsPGroup 2 SL := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hSLi : ¬ 2 ∣ SL.index := hS.2.2
  have hSX2 : IsPGroup 2 (SL.map θ0) := hSL2.map θ0
  have hSXi : ¬ 2 ∣ (SL.map θ0).index := fun h => hSLi (h.trans (Subgroup.index_map_dvd SL hθ0))
  obtain ⟨x, hx⟩ := exists_conj_of_sylow_two hSX2 hSXi hS₀ hS₀i
  let θ : ↥L →* X := (MulAut.conj x).toMonoidHom.comp θ0
  have hθ : Function.Surjective θ := (MulAut.conj x).surjective.comp hθ0
  have hθker : θ.ker = θ0.ker := by
    ext l
    simp [θ, MonoidHom.mem_ker]
  have hθS : SL.map θ = S₀ := by
    rw [← hx, ← Subgroup.map_map]
  have hind : ∀ (r : G) (hr : r ∈ R), ∃ cbar : MulAut X, S₀.map cbar.toMonoidHom = S₀ ∧
      ∀ l : ↥L, cbar (θ l) = θ (L.normalizerMonoidHom ⟨r, hRN hr⟩ l) := by
    intro r hr
    set c : MulAut ↥L := L.normalizerMonoidHom ⟨r, hRN hr⟩ with hc
    have hkerc : θ.ker.comap c.toMonoidHom = θ.ker := by
      rw [hθker, hker]
      exact (Subgroup.Characteristic.fixed (H := CFSG.pCore 2 ↥L) inferInstance c)
    obtain ⟨cbar, hcbar⟩ := exists_induced_mulAut θ hθ c hkerc
    have hSc : SL.map c.toMonoidHom = SL := by
      ext y
      constructor
      · rintro ⟨l, hl, rfl⟩
        have hl' : (l : G) ∈ R ⊓ L := hl
        have : ((c l : ↥L) : G) ∈ R ⊓ L :=
          ⟨(conj_mem_sylow_iff hRN hr l).2 hl'.1, (c l).2⟩
        exact this
      · intro hy
        have hy' : (y : G) ∈ R ⊓ L := hy
        refine ⟨c.symm y, ?_, by simp⟩
        have h1 : ((c (c.symm y) : ↥L) : G) ∈ R := by simpa using hy'.1
        show ((c.symm y : ↥L) : G) ∈ R ⊓ L
        exact ⟨(conj_mem_sylow_iff hRN hr (c.symm y)).1 h1, (c.symm y).2⟩
    refine ⟨cbar, ?_, hcbar⟩
    rw [← hθS, Subgroup.map_map]
    have : cbar.toMonoidHom.comp θ = θ.comp c.toMonoidHom := by
      ext l
      exact hcbar l
    rw [this, ← Subgroup.map_map, hSc]
  have one : ∀ K : Subgroup X, (∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ →
      K.map α.toMonoidHom = K) → K ≠ ⊤ → GoodLocal K →
      (K.comap θ).map L.subtype ≤ L ∧
      R ≤ Subgroup.normalizer (((K.comap θ).map L.subtype : Subgroup G) : Set G) ∧
      (K.comap θ).map L.subtype ≠ L ∧ CharTwo ((K.comap θ).map L.subtype) ∧
      ¬ HasChi0Block ((K.comap θ).map L.subtype) := by
    intro K hKinv hKne hKgood
    have hmem : ∀ g : G, g ∈ (K.comap θ).map L.subtype ↔ ∃ hg : g ∈ L, θ ⟨g, hg⟩ ∈ K := by
      intro g
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l.2, hl⟩
      · rintro ⟨hg, h⟩
        exact ⟨⟨g, hg⟩, h, rfl⟩
    have hkey : ∀ r ∈ R, ∀ g ∈ (K.comap θ).map L.subtype,
        r * g * r⁻¹ ∈ (K.comap θ).map L.subtype := by
      intro r hr g hg
      obtain ⟨hgL, hgK⟩ := (hmem g).1 hg
      obtain ⟨cbar, hS₀c, hcbar⟩ := hind r hr
      have hKc := hKinv cbar hS₀c
      have hgL' : r * g * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hRN hr) g).1 hgL
      refine (hmem _).2 ⟨hgL', ?_⟩
      have h1 : θ ⟨r * g * r⁻¹, hgL'⟩ = cbar (θ ⟨g, hgL⟩) := by
        rw [hcbar]
        rfl
      have h2 : cbar (θ ⟨g, hgL⟩) ∈ K.map cbar.toMonoidHom := ⟨θ ⟨g, hgL⟩, hgK, rfl⟩
      rw [hKc] at h2
      rw [h1]
      exact h2
    refine ⟨fun g hg => ((hmem g).1 hg).1, ?_, ?_, ?_⟩
    · intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro g
      refine ⟨hkey r hr g, fun hg => ?_⟩
      have := hkey r⁻¹ (R.inv_mem hr) _ hg
      simpa [mul_assoc] using this
    · intro hi
      apply hKne
      rw [eq_top_iff]
      intro y _
      obtain ⟨l, rfl⟩ := hθ y
      have : (l : G) ∈ (K.comap θ).map L.subtype := by rw [hi]; exact l.2
      obtain ⟨hg, h⟩ := (hmem l).1 this
      exact h
    · let φ : ↥((K.comap θ).map L.subtype) →* ↥K :=
        { toFun := fun g => ⟨θ ⟨g.1, ((hmem g.1).1 g.2).1⟩, ((hmem g.1).1 g.2).2⟩
          map_one' := Subtype.ext (map_one θ)
          map_mul' := fun a b => Subtype.ext (map_mul θ ⟨a.1, ((hmem a.1).1 a.2).1⟩
            ⟨b.1, ((hmem b.1).1 b.2).1⟩) }
      have hφs : Function.Surjective φ := by
        rintro ⟨y, hy⟩
        obtain ⟨l, rfl⟩ := hθ y
        have hlK : (l : G) ∈ (K.comap θ).map L.subtype := (hmem l).2 ⟨l.2, hy⟩
        exact ⟨⟨l, hlK⟩, rfl⟩
      have hφk : IsPGroup 2 φ.ker := by
        intro k
        have hk : θ ⟨(k : ↥((K.comap θ).map L.subtype)).1,
            ((hmem (k : ↥((K.comap θ).map L.subtype)).1).1 (k : ↥((K.comap θ).map L.subtype)).2).1⟩
            = 1 := by
          have := k.2
          rw [MonoidHom.mem_ker] at this
          exact congrArg Subtype.val this
        have hmemker : (⟨(k : ↥((K.comap θ).map L.subtype)).1,
            ((hmem (k : ↥((K.comap θ).map L.subtype)).1).1
              (k : ↥((K.comap θ).map L.subtype)).2).1⟩ : ↥L) ∈ θ0.ker := by
          rw [← hθker]
          exact hk
        obtain ⟨n, hn⟩ := hNker2 ⟨_, hmemker⟩
        refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg (fun y : ↥θ0.ker => ((y : ↥L) : G)) hn
        simpa using this
      exact hKgood G _ φ hφs hφk
  obtain ⟨hle₁, hnorm₁, hne₁', hc₁, hb₁⟩ := one K₁ hinv₁ hne₁ hg₁
  obtain ⟨hle₂, hnorm₂, hne₂', hc₂, hb₂⟩ := one K₂ hinv₂ hne₂ hg₂
  refine ⟨_, _, hle₁, hle₂, hne₁', hne₂', ?_, hnorm₁, hnorm₂, hc₁, hc₂, hb₁, hb₂⟩
  apply le_antisymm (sup_le hle₁ hle₂)
  intro g hg
  have h1 : (⟨g, hg⟩ : ↥L) ∈ (K₁.comap θ) ⊔ (K₂.comap θ) := by
    rw [Subgroup.comap_sup_eq_of_le_range θ (by rw [MonoidHom.range_eq_top.2 hθ]; exact le_top)
      (by rw [MonoidHom.range_eq_top.2 hθ]; exact le_top), hsup]
    exact Subgroup.mem_top _
  have h2 : ((K₁.comap θ) ⊔ (K₂.comap θ)).map L.subtype ≤
      (K₁.comap θ).map L.subtype ⊔ (K₂.comap θ).map L.subtype := by
    rw [Subgroup.map_sup]
  exact h2 ⟨⟨g, hg⟩, h1, rfl⟩

end CFSG.QuasithinUnique.Vol2Native.L239
