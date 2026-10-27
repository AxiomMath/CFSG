module

public import CFSG.CGT.PushingUpLit.BHS6.SymLocalPerm
public import CFSG.CGT.PushingUpLit.BHS.CStar
public import CFSG.CGT.PushingUpLit.BHS6.SixEightGen

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {n : ℕ}

@[expose] def preimG (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n))
    (Y : Subgroup (Equiv.Perm (Fin n))) : Subgroup Γ :=
  (Y.comap φ).map G.subtype

theorem mem_preimG {G : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)}
    {Y : Subgroup (Equiv.Perm (Fin n))} {g : Γ} :
    g ∈ preimG G φ Y ↔ ∃ hg : g ∈ G, φ ⟨g, hg⟩ ∈ Y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨g, h⟩, hx, rfl⟩

theorem preimG_le (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n))
    (Y : Subgroup (Equiv.Perm (Fin n))) : preimG G φ Y ≤ G := fun _ hx => (mem_preimG.1 hx).1

theorem preimG_mono (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n))
    {Y Y' : Subgroup (Equiv.Perm (Fin n))} (h : Y ≤ Y') : preimG G φ Y ≤ preimG G φ Y' := by
  intro g hg
  obtain ⟨hgG, hgY⟩ := mem_preimG.1 hg
  exact mem_preimG.2 ⟨hgG, h hgY⟩

theorem mem_preimG_of_map_eq_one {G : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)}
    {Y : Subgroup (Equiv.Perm (Fin n))} {g : Γ} (hg : g ∈ G) (h : φ ⟨g, hg⟩ = 1) :
    g ∈ preimG G φ Y :=
  mem_preimG.2 ⟨hg, h ▸ Y.one_mem⟩

@[expose] def imgG (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) (S : Subgroup Γ) :
    Subgroup (Equiv.Perm (Fin n)) := (S.subgroupOf G).map φ

theorem mem_imgG {G : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)} {S : Subgroup Γ}
    {σ : Equiv.Perm (Fin n)} : σ ∈ imgG G φ S ↔ ∃ (g : Γ) (hg : g ∈ G), g ∈ S ∧ φ ⟨g, hg⟩ = σ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, y.2, hy, rfl⟩
  · rintro ⟨g, hg, hgS, rfl⟩
    exact ⟨⟨g, hg⟩, hgS, rfl⟩

theorem isPGroup_imgG {G : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)} {S : Subgroup Γ}
    (hSG : S ≤ G) (hS : IsPGroup 2 ↥S) : IsPGroup 2 ↥(imgG G φ S) :=
  (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSG).symm).map φ

theorem imgG_mono (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) {S S' : Subgroup Γ}
    (h : S ≤ S') : imgG G φ S ≤ imgG G φ S' := by
  intro σ hσ
  obtain ⟨g, hg, hgS, rfl⟩ := mem_imgG.1 hσ
  exact mem_imgG.2 ⟨g, hg, h hgS, rfl⟩

@[expose] def kerG (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) : Subgroup Γ :=
  φ.ker.map G.subtype

theorem mem_kerG {G : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)} {g : Γ} :
    g ∈ kerG G φ ↔ ∃ hg : g ∈ G, φ ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨g, h⟩, hx, rfl⟩

theorem le_normalizer_kerG (G : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) :
    G ≤ Subgroup.normalizer (kerG G φ : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g' ∈ G, ∀ h ∈ kerG G φ, g' * h * g'⁻¹ ∈ kerG G φ := by
    intro g' hg' h hh
    obtain ⟨hhG, hh1⟩ := mem_kerG.1 hh
    refine mem_kerG.2 ⟨G.mul_mem (G.mul_mem hg' hhG) (G.inv_mem hg'), ?_⟩
    have e : (⟨g' * h * g'⁻¹, G.mul_mem (G.mul_mem hg' hhG) (G.inv_mem hg')⟩ : ↥G) =
        ⟨g', hg'⟩ * ⟨h, hhG⟩ * ⟨g', hg'⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hh1]
    simp
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (G.inv_mem hg) _ hh
  simpa [mul_assoc] using this

section Sylow

variable [Finite Γ]

theorem isSylowTwoOf_preimG_inf {G T : Subgroup Γ} (hT : IsSylowTwoOf T G)
    (φ : ↥G →* Equiv.Perm (Fin n)) (Y : Subgroup (Equiv.Perm (Fin n)))
    (hmax : ∀ P : Subgroup (Equiv.Perm (Fin n)), P ≤ Y → IsPGroup 2 ↥P →
      imgG G φ T ⊓ Y ≤ P → P ≤ imgG G φ T ⊓ Y) :
    IsSylowTwoOf (T ⊓ preimG G φ Y) (preimG G φ Y) := by
  classical
  set L : Subgroup Γ := preimG G φ Y with hL
  have hLG : L ≤ G := preimG_le G φ Y
  have hKL : kerG G φ ≤ L := fun g hg => by
    obtain ⟨hgG, hg1⟩ := mem_kerG.1 hg
    exact mem_preimG_of_map_eq_one hgG hg1
  have hKG : kerG G φ ≤ G := fun g hg => (mem_kerG.1 hg).1
  have hK : IsSylowTwoOf (T ⊓ kerG G φ) (kerG G φ) :=
    B6.isSylowTwoOf_inf_normal hT hKG (le_normalizer_kerG G φ)
  refine A4.isSylowTwoOf_iff_maximal.2
    ⟨inf_le_right, hT.2.1.to_le inf_le_left, fun P hPL hP hSP => ?_⟩
  intro x hx
  obtain ⟨hxG, hxY⟩ := mem_preimG.1 (hPL hx)
  have hPG : P ≤ G := hPL.trans hLG
  have hPimgY : imgG G φ P ≤ Y := by
    intro σ hσ
    obtain ⟨g, hg, hgP, rfl⟩ := mem_imgG.1 hσ
    exact (mem_preimG.1 (hPL hgP)).2
  have hsup : imgG G φ T ⊓ Y ≤ imgG G φ P := by
    intro σ hσ
    obtain ⟨g, hg, hgT, rfl⟩ := mem_imgG.1 hσ.1
    have hgL : g ∈ L := mem_preimG.2 ⟨hg, hσ.2⟩
    exact mem_imgG.2 ⟨g, hg, hSP ⟨hgT, hgL⟩, rfl⟩
  have hle := hmax (imgG G φ P) hPimgY (isPGroup_imgG hPG hP) hsup
  have hxim : φ ⟨x, hxG⟩ ∈ imgG G φ T ⊓ Y := hle (mem_imgG.2 ⟨x, hxG, hx, rfl⟩)
  obtain ⟨t, htG, htT, hteq⟩ := mem_imgG.1 hxim.1
  have htL : t ∈ L := mem_preimG.2 ⟨htG, hteq ▸ hxim.2⟩
  have htS : t ∈ T ⊓ L := ⟨htT, htL⟩
  have htP : t ∈ P := hSP htS
  have htx : t⁻¹ * x ∈ P ⊓ kerG G φ := by
    refine ⟨P.mul_mem (P.inv_mem htP) hx, mem_kerG.2 ⟨G.mul_mem (G.inv_mem htG) hxG, ?_⟩⟩
    have e : (⟨t⁻¹ * x, G.mul_mem (G.inv_mem htG) hxG⟩ : ↥G) = ⟨t, htG⟩⁻¹ * ⟨x, hxG⟩ := rfl
    rw [e, map_mul, map_inv, hteq]
    simp
  have hKP : P ⊓ kerG G φ ≤ T ⊓ kerG G φ := by
    obtain ⟨-, -, hKmax⟩ := A4.isSylowTwoOf_iff_maximal.1 hK
    have hTK : T ⊓ kerG G φ ≤ P ⊓ kerG G φ := fun g hg => ⟨hSP ⟨hg.1, hKL hg.2⟩, hg.2⟩
    exact hKmax (P ⊓ kerG G φ) inf_le_right (hP.to_le inf_le_left) hTK
  have htx' : t⁻¹ * x ∈ T := (hKP htx).1
  have hxT : x ∈ T := by
    have := T.mul_mem htT htx'
    simpa using this
  exact ⟨hxT, hPL hx⟩

end Sylow

section Frattini

variable [Finite Γ]

open scoped Pointwise in
theorem exists_mem_normalizer_baum_of_mem_normalizer {G T : Subgroup Γ} (hT : IsSylowTwoOf T G)
    (φ : ↥G →* Equiv.Perm (Fin n)) (hφs : Function.Surjective φ) {π : Equiv.Perm (Fin n)}
    (hπ : π ∈ Subgroup.normalizer (imgG G φ (baum T) : Set (Equiv.Perm (Fin n)))) :
    ∃ (g : Γ) (hg : g ∈ G), g ∈ Subgroup.normalizer (baum T : Set Γ) ∧ φ ⟨g, hg⟩ = π := by
  classical
  obtain ⟨g₀, hg₀⟩ := hφs π
  set Bbar : Subgroup (Equiv.Perm (Fin n)) := imgG G φ (baum T) with hBbar
  have hBT : baum T ≤ T := inf_le_left
  have hBG : baum T ≤ G := hBT.trans hT.1
  have hBTim : Bbar ≤ imgG G φ T := imgG_mono G φ hBT
  set LB : Subgroup Γ := preimG G φ Bbar with hLB
  have hLBG : LB ≤ G := preimG_le G φ Bbar
  have hSyl : IsSylowTwoOf (T ⊓ LB) LB :=
    isSylowTwoOf_preimG_inf hT φ Bbar fun P hPY _ _ => le_inf (hPY.trans hBTim) hPY
  have hbL : baum T ≤ LB := fun b hb =>
    mem_preimG.2 ⟨hBG hb, mem_imgG.2 ⟨b, hBG hb, hb, rfl⟩⟩
  have hbTB : baum T ≤ T ⊓ LB := le_inf hBT hbL
  have hπmem : ∀ h, h ∈ Bbar ↔ π * h * π⁻¹ ∈ Bbar := Subgroup.mem_normalizer_iff.mp hπ
  have hconj : ∀ x : Γ, ∀ hx : x ∈ G, ∀ hy : (g₀ : Γ) * x * (g₀ : Γ)⁻¹ ∈ G,
      φ ⟨(g₀ : Γ) * x * (g₀ : Γ)⁻¹, hy⟩ = π * φ ⟨x, hx⟩ * π⁻¹ := by
    intro x hx hy
    have e : (⟨(g₀ : Γ) * x * (g₀ : Γ)⁻¹, hy⟩ : ↥G) = g₀ * ⟨x, hx⟩ * g₀⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hg₀]
  have hconjLB : ∀ x : Γ, x ∈ LB ↔ (g₀ : Γ) * x * (g₀ : Γ)⁻¹ ∈ LB := by
    intro x
    constructor
    · intro hx
      obtain ⟨hxG, hxB⟩ := mem_preimG.1 hx
      have hy : (g₀ : Γ) * x * (g₀ : Γ)⁻¹ ∈ G := G.mul_mem (G.mul_mem g₀.2 hxG) (G.inv_mem g₀.2)
      exact mem_preimG.2 ⟨hy, by rw [hconj x hxG hy]; exact (hπmem _).1 hxB⟩
    · intro hx
      obtain ⟨hyG, hyB⟩ := mem_preimG.1 hx
      have hxG : x ∈ G := by
        have := G.mul_mem (G.mul_mem (G.inv_mem g₀.2) hyG) g₀.2
        simpa [mul_assoc] using this
      refine mem_preimG.2 ⟨hxG, ?_⟩
      rw [hconj x hxG hyG] at hyB
      exact (hπmem _).2 hyB
  have hmapLB : LB.map (MulAut.conj (g₀ : Γ)).toMonoidHom = LB := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hconjLB x).1 hx
    · intro hy
      refine ⟨(g₀ : Γ)⁻¹ * y * (g₀ : Γ), ?_, by simp [mul_assoc]⟩
      show (g₀ : Γ)⁻¹ * y * (g₀ : Γ) ∈ LB
      rw [hconjLB]
      simpa [mul_assoc] using hy
  have hSyl' : IsSylowTwoOf ((T ⊓ LB).map (MulAut.conj (g₀ : Γ)).toMonoidHom) LB := by
    have := hSyl.map_equiv (MulAut.conj (g₀ : Γ))
    rwa [hmapLB] at this
  obtain ⟨l, hlLB, hl⟩ := hSyl.exists_conj hSyl'
  have hlG : l ∈ G := hLBG hlLB
  have hgN : (l⁻¹ * (g₀ : Γ)) ∈ Subgroup.normalizer ((T ⊓ LB : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : (g₀ : Γ) * h * (g₀ : Γ)⁻¹ ∈ (T ⊓ LB).map (MulAut.conj (g₀ : Γ)).toMonoidHom :=
        ⟨h, hh, rfl⟩
      rw [hl] at h1
      obtain ⟨s', hs', hs'e⟩ := h1
      have : l⁻¹ * (g₀ : Γ) * h * ((l⁻¹ * (g₀ : Γ))⁻¹) = s' := by
        have e1 : l * s' * l⁻¹ = (g₀ : Γ) * h * (g₀ : Γ)⁻¹ := hs'e
        calc l⁻¹ * (g₀ : Γ) * h * ((l⁻¹ * (g₀ : Γ))⁻¹)
            = l⁻¹ * ((g₀ : Γ) * h * (g₀ : Γ)⁻¹) * l := by group
          _ = l⁻¹ * (l * s' * l⁻¹) * l := by rw [e1]
          _ = s' := by group
      rw [this]
      exact hs'
    · intro hh
      have h1 : l * (l⁻¹ * (g₀ : Γ) * h * ((l⁻¹ * (g₀ : Γ))⁻¹)) * l⁻¹ ∈
          (T ⊓ LB).map (MulAut.conj l).toMonoidHom := ⟨_, hh, rfl⟩
      have e2 : l * (l⁻¹ * (g₀ : Γ) * h * ((l⁻¹ * (g₀ : Γ))⁻¹)) * l⁻¹ =
          (g₀ : Γ) * h * (g₀ : Γ)⁻¹ := by group
      rw [e2, ← hl] at h1
      obtain ⟨s', hs', hs'e⟩ := h1
      have : h = s' := by
        have e3 : (g₀ : Γ) * s' * (g₀ : Γ)⁻¹ = (g₀ : Γ) * h * (g₀ : Γ)⁻¹ := hs'e
        have := mul_left_cancel (mul_right_cancel e3)
        exact this.symm
      rw [this]
      exact hs'
  have hbaumeq : baum T = baum (T ⊓ LB) := baum_eq_of_le hbTB inf_le_left
  have hgNb : (l⁻¹ * (g₀ : Γ)) ∈ Subgroup.normalizer (baum T : Set Γ) := by
    have := normalizer_le_normalizer_baum (T ⊓ LB) hgN
    rwa [← hbaumeq] at this
  obtain ⟨hlG', hlB⟩ := mem_preimG.1 hlLB
  obtain ⟨b, hbG, hbB, hbl⟩ := mem_imgG.1 hlB
  have hbN : b ∈ Subgroup.normalizer (baum T : Set Γ) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)) (hBT hbB)
  have hgG : l⁻¹ * (g₀ : Γ) ∈ G := G.mul_mem (G.inv_mem hlG) g₀.2
  refine ⟨b * (l⁻¹ * (g₀ : Γ)), G.mul_mem hbG hgG, Subgroup.mul_mem _ hbN hgNb, ?_⟩
  have e : (⟨b * (l⁻¹ * (g₀ : Γ)), G.mul_mem hbG hgG⟩ : ↥G) =
      ⟨b, hbG⟩ * (⟨l, hlG⟩⁻¹ * g₀) := rfl
  rw [e, map_mul, map_mul, map_inv, hg₀]
  have : φ ⟨b, hbG⟩ = φ ⟨l, hlG⟩ := by
    have h2 := hbl
    simpa using h2
  rw [this]
  simp

end Frattini

section CStar

variable [Finite Γ]

theorem eq_top_of_alt_le_of_odd {H : Subgroup (Equiv.Perm (Fin n))}
    (hA : alternatingGroup (Fin n) ≤ H) {t : Equiv.Perm (Fin n)} (ht : t ∈ H)
    (hodd : Equiv.Perm.sign t = -1) : H = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact hA (Equiv.Perm.mem_alternatingGroup.2 h)
  · have h1 : σ * t ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, h, hodd]
      decide
    have := H.mul_mem (hA h1) (H.inv_mem ht)
    simpa using this

theorem not_preimG_le_cStarIn {G T : Subgroup Γ} (hT : IsSylowTwoOf T G)
    (hne : cStarIn G T ≠ G) (φ : ↥G →* Equiv.Perm (Fin n)) (hφs : Function.Surjective φ)
    (hn : Odd n)
    (hK : ∀ (g : Γ) (hg : g ∈ G), φ ⟨g, hg⟩ = 1 → g ∈ cStarIn G T)
    {T' : Set (Equiv.Perm (Fin n))} (hT'ne : T'.Nonempty) (hs : ∀ t ∈ T', t.IsSwap)
    (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
    (hT'B : imgG G φ (baum T) = Subgroup.closure T')
    {t : Equiv.Perm (Fin n)} (ht : t ∈ T') {x : Fin n} (hx : t x ≠ x) {c : Fin n}
    (hcf : ∀ s ∈ T', s c = c) :
    ¬ preimG G φ (Subgroup.closure T' ⊔ Subgroup.zpowers (cyc x (t x) c)) ≤ cStarIn G T := by
  classical
  intro hL
  set C : Subgroup Γ := cStarIn G T with hC
  have hCG : C ≤ G := cStarIn_le G T
  set H : Subgroup (Equiv.Perm (Fin n)) := imgG G φ C with hH
  have hb0 : baum T ≠ ⊥ := by
    intro h0
    have h1 : t ∈ imgG G φ (baum T) := by
      rw [hT'B]
      exact Subgroup.subset_closure ht
    obtain ⟨g, hg, hgB, hgt⟩ := mem_imgG.1 h1
    rw [h0, Subgroup.mem_bot] at hgB
    subst hgB
    have h1' : (⟨(1 : Γ), hg⟩ : ↥G) = 1 := rfl
    rw [h1', map_one] at hgt
    obtain ⟨a, b, hab, rfl⟩ := hs _ ht
    have := congrArg (fun f : Equiv.Perm (Fin n) => f a) hgt
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at this
    exact hab this
  have hNC : G ⊓ Subgroup.normalizer (baum T : Set Γ) ≤ C := inf_normalizer_baum_le_cStarIn hb0
  have hdH : cyc x (t x) c ∈ H := by
    obtain ⟨g, hg⟩ := hφs (cyc x (t x) c)
    have hgL : (g : Γ) ∈ preimG G φ (Subgroup.closure T' ⊔ Subgroup.zpowers (cyc x (t x) c)) :=
      mem_preimG.2 ⟨g.2, by
        rw [show φ ⟨(g : Γ), g.2⟩ = cyc x (t x) c from hg]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
    exact mem_imgG.2 ⟨g, g.2, hL hgL, hg⟩
  have hcycH : ∀ t' ∈ T', ∀ x', t' x' ≠ x' → ∀ c', (∀ s ∈ T', s c' = c') →
      cyc x' (t' x') c' ∈ H := by
    intro t' ht' x' hx' c' hcf'
    obtain ⟨π, hπN, hπ⟩ := exists_normalizer_conj_cyc hs hc ht hx hcf ht' hx' hcf'
    rw [← hT'B] at hπN
    obtain ⟨g', hg'G, hg'N, hg'φ⟩ :=
      exists_mem_normalizer_baum_of_mem_normalizer hT φ hφs hπN
    have hg'C : g' ∈ C := hNC ⟨hg'G, hg'N⟩
    obtain ⟨d, hdG, hdC, hdφ⟩ := mem_imgG.1 hdH
    have hconjC : g' * d * g'⁻¹ ∈ C := C.mul_mem (C.mul_mem hg'C hdC) (C.inv_mem hg'C)
    have hconjG : g' * d * g'⁻¹ ∈ G := hCG hconjC
    refine mem_imgG.2 ⟨g' * d * g'⁻¹, hconjG, hconjC, ?_⟩
    have e : (⟨g' * d * g'⁻¹, hconjG⟩ : ↥G) = ⟨g', hg'G⟩ * ⟨d, hdG⟩ * ⟨g', hg'G⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hg'φ, hdφ]
    exact hπ
  have hAH : alternatingGroup (Fin n) ≤ H :=
    alternatingGroup_le_of_cyc_mem H hs hc hT'ne (exists_fixed_of_swaps hn hs hc) hcycH
  have htH : t ∈ H := by
    have h1 : t ∈ imgG G φ (baum T) := by
      rw [hT'B]
      exact Subgroup.subset_closure ht
    obtain ⟨g, hg, hgB, hgt⟩ := mem_imgG.1 h1
    exact mem_imgG.2 ⟨g, hg, hNC ⟨hg, Subgroup.le_normalizer hgB⟩, hgt⟩
  have htodd : Equiv.Perm.sign t = -1 := by
    obtain ⟨a, b, hab, rfl⟩ := hs t ht
    exact Equiv.Perm.sign_swap hab
  have hHtop : H = ⊤ := eq_top_of_alt_le_of_odd hAH htH htodd
  apply hne
  refine le_antisymm hCG fun g hg => ?_
  have : φ ⟨g, hg⟩ ∈ H := hHtop ▸ Subgroup.mem_top _
  obtain ⟨c', hc'G, hc'C, hc'φ⟩ := mem_imgG.1 this
  have hker : c'⁻¹ * g ∈ C := by
    refine hK _ (G.mul_mem (G.inv_mem hc'G) hg) ?_
    have e : (⟨c'⁻¹ * g, G.mul_mem (G.inv_mem hc'G) hg⟩ : ↥G) =
        ⟨c', hc'G⟩⁻¹ * ⟨g, hg⟩ := rfl
    rw [e, map_mul, map_inv, hc'φ]
    simp
  have := C.mul_mem hc'C hker
  simpa using this

end CStar

end CFSG.CGT.PushingUpLit.BHS6
