module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecXg

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

set_option linter.unusedSectionVars false

namespace Twin1711

section General

variable {G : Type} [Group G]

@[expose] def conjAut (X : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (X : Set G)) :
    MulAut ↥X where
  toFun y := ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha y).mp y.2⟩
  invFun y := ⟨a⁻¹ * y * a, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem ha) y).mp y.2
    simpa using this⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' y y' := by ext; simp [mul_assoc]

theorem conjAut_apply (X : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (X : Set G))
    (y : ↥X) : ((conjAut X a ha y : ↥X) : G) = a * y * a⁻¹ := rfl

theorem conjAut_mul (X : Subgroup G) (a b : G) (ha : a ∈ Subgroup.normalizer (X : Set G))
    (hb : b ∈ Subgroup.normalizer (X : Set G)) :
    conjAut X (a * b) (Subgroup.mul_mem _ ha hb) = conjAut X a ha * conjAut X b hb := by
  ext y; simp [conjAut_apply, mul_assoc]

theorem conjAut_eq_one_iff (X : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (X : Set G)) :
    conjAut X a ha = 1 ↔ ∀ y ∈ X, a * y = y * a := by
  constructor
  · intro h y hy
    have := congrArg (fun α : MulAut ↥X => ((α ⟨y, hy⟩ : ↥X) : G)) h
    simp only [conjAut_apply] at this
    have h2 : a * y * a⁻¹ = y := this
    calc a * y = a * y * a⁻¹ * a := by group
      _ = y * a := by rw [h2]
  · intro h
    ext y
    show a * (y : G) * a⁻¹ = y
    rw [h y y.2]; group

theorem relIndex_le_card_fixSet [Finite G] (X T N : Subgroup G) (B : Set (Subgroup G)) (w : G)
    (hT : ∀ s ∈ T, w * s * w⁻¹ ∈ Subgroup.normalizer (X : Set G))
    (hN : ∀ s ∈ T, s ∈ N ↔ ∀ y ∈ X, (w * s * w⁻¹) * y = y * (w * s * w⁻¹))
    (hB : ∀ s ∈ T, ∀ b ∈ B, ∀ y : ↥X, (y : G) ∈ b → (w * s * w⁻¹) * y * (w * s * w⁻¹)⁻¹ = y) :
    N.relIndex T ≤ Nat.card (fixSet X B) := by
  classical
  let φ : ↥T →* MulAut ↥X :=
    MonoidHom.mk' (fun s => conjAut X (w * s * w⁻¹) (hT s s.2)) (by
      intro a b
      have : w * ((a : G) * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
      simp only [Subgroup.coe_mul]
      rw [← conjAut_mul X _ _ (hT a a.2) (hT b b.2)]
      congr 1)
  have hker : φ.ker = N.subgroupOf T := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show conjAut X (w * s * w⁻¹) (hT s s.2) = 1 ↔ (s : G) ∈ N
    rw [conjAut_eq_one_iff, ← hN s s.2]
  have hrange : φ.range ≤ (fixSet X B).comap (MonoidHom.id _) := by
    rintro _ ⟨s, rfl⟩ b hb y hy
    ext
    exact hB s s.2 b hb y hy
  have h1 : N.relIndex T = Nat.card (↥T ⧸ φ.ker) := by
    rw [hker]; rfl
  rw [h1, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  exact Subgroup.card_le_of_le hrange

end General

section Config

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure Cfg (Ω : Set (Subgroup G)) (K : Subgroup G) (π : Set (Subgroup G)) (z g : G) : Prop where
  std : OrbitStd Ω
  trans : ∀ J ∈ Ω, ∃ h : G, conjSub h K = J
  gen : (⨆ L ∈ Ω, L) = ⊤
  center : Subgroup.center G = ⊥
  mem : K ∈ Ω
  max : π ∈ maxOrbs (nbrAdj Ω) K
  h1 : NoCentralInv π
  inv : IsUniqueInvolution K z
  q8 : Nonempty (↥K ≃* QuaternionGroup 2)

structure Cfg' (Ω : Set (Subgroup G)) (K : Subgroup G) (π : Set (Subgroup G)) (z g : G) : Prop
    extends Cfg Ω K π z g where
  conj : conjSub g K ∈ π

noncomputable def conjSubEquiv (K : Subgroup G) (g : G) : ↥K ≃* ↥(conjSub g K) :=
  Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

variable {K : Subgroup G} {π : Set (Subgroup G)} {z g : G}

theorem Cfg'.swap (h : Cfg' Ω K π z g) :
    Cfg' Ω (conjSub g K) (conjSub g '' π) (g * z * g⁻¹) g⁻¹ where
  std := h.std
  trans J hJ := by
    obtain ⟨c, rfl⟩ := h.trans J hJ
    exact ⟨c * g⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  gen := h.gen
  center := h.center
  mem := h.std.graph.conjMem K h.mem g
  max := isMaxOrb_conj h.std.graph h.max g
  h1 := h.h1.conj g
  inv := h.inv.conj g
  q8 := ⟨(conjSubEquiv K g).symm.trans h.q8.some⟩
  conj := by
    rw [conjSub_inv_conjSub]
    exact h.std.mem_conj_image_of_mem h.max h.conj

theorem Cfg'.xOrbit_eq (h : Cfg' Ω K π z g) : xOrbit (piGen π) (conjSub g K) = π := by
  ext J
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact stable_of_maxOrb h.std.graph h.max x hx _ h.conj
  · intro hJ
    obtain ⟨a, ha, hJ'⟩ := transitive_of_maxOrb h.std.graph h.max _ h.conj J hJ
    exact ⟨a, ha, hJ'⟩

theorem Cfg'.conj_inv_mem (h : Cfg' Ω K π z g) : conjSub g⁻¹ K ∈ π := by
  obtain ⟨J, hJ, hJK⟩ := h.std.mem_conj_image_of_mem h.max h.conj
  have : J = conjSub g⁻¹ K := by rw [← hJK, conjSub_inv_conjSub]
  rwa [← this]

theorem Cfg'.translate_eq (h : Cfg' Ω K π z g) {a b : G} (hab : conjSub a K = conjSub b K) :
    conjSub a '' betaOf (nbrAdj Ω) Ω π = conjSub b '' betaOf (nbrAdj Ω) Ω π := by
  have hK : K ∈ betaOf (nbrAdj Ω) Ω π := ⟨h.mem, fun M hM => adj_of_mem_isMaxOrb h.std.graph h.max hM⟩
  have hc : conjSub (b⁻¹ * a) K = K := by
    rw [conjSub_mul, hab, conjSub_inv_conjSub]
  have hblock := block_betaOf h.std.graph h.mem h.max (b⁻¹ * a)
  have hceq : conjSub (b⁻¹ * a) '' betaOf (nbrAdj Ω) Ω π = betaOf (nbrAdj Ω) Ω π := by
    rcases hblock with h1 | h1
    · exact h1
    · exfalso
      exact Set.disjoint_left.mp h1 ⟨K, hK, hc⟩ hK
  calc conjSub a '' betaOf (nbrAdj Ω) Ω π
      = conjSub b '' (conjSub (b⁻¹ * a) '' betaOf (nbrAdj Ω) Ω π) := by
        rw [Set.image_image]
        congr 1
        ext1 J
        rw [← conjSub_mul]
        simp
    _ = conjSub b '' betaOf (nbrAdj Ω) Ω π := by rw [hceq]

theorem Cfg'.generate (h : Cfg' Ω K π z g) :
    (⨆ M ∈ π ∪ conjSub g '' π, M) = ⊤ :=
  (graph_17_10 h.std.graph h.mem h.max).generate h.gen g h.conj

theorem Cfg'.beta_conj (h : Cfg' Ω K π z g) :
    conjSub g '' betaOf (nbrAdj Ω) Ω π = betaOf (nbrAdj Ω) Ω (conjSub g '' π) :=
  conj_betaOf h.std.graph π g

theorem Cfg'.R_le (h : Cfg' Ω K π z g) : conjSub g K ≤ piGen π := le_piGen h.conj

theorem Cfg'.R_inv (h : Cfg' Ω K π z g) : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) :=
  h.inv.conj g

theorem Cfg'.R_mem (h : Cfg' Ω K π z g) : conjSub g K ∈ Ω := h.std.graph.conjMem K h.mem g

theorem Cfg'.Y_eq (π : Set (Subgroup G)) (g : G) :
    conjSub g (piGen π) = piGen (conjSub g '' π) := (piGen_conj π g).symm

theorem Cfg'.twin_mem_B (h : Cfg' Ω K π z g) {s : G}
    (hs : s ∈ piGen π ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :
    conjSub s (conjSub g K) ∈ conjSub g '' betaOf (nbrAdj Ω) Ω π := by
  have hsc : s * (g * z * g⁻¹) * s⁻¹ = g * z * g⁻¹ := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hs.2
    rw [this, mul_inv_cancel_right]
  have hR := h.R_inv
  have hRs : IsUniqueInvolution (conjSub s (conjSub g K)) (g * z * g⁻¹) := by
    have := hR.conj s
    rwa [hsc] at this
  have hΩ : conjSub s (conjSub g K) ∈ Ω := h.std.graph.conjMem _ h.R_mem s
  have := h.swap.std.twinSet_subset_beta h.swap.max h.swap.h1
    (show conjSub s (conjSub g K) ∈ twinSet Ω (conjSub g K) from ⟨hΩ, _, hR, hRs⟩)
  rwa [← h.beta_conj] at this

theorem Cfg'.B_le_centralizer (h : Cfg' Ω K π z g) {v : Subgroup G}
    (hv : v ∈ conjSub g '' betaOf (nbrAdj Ω) Ω π) :
    v ≤ Subgroup.centralizer (conjSub g (piGen π) : Set G) := by
  rw [h.beta_conj] at hv
  have := h.swap.std.beta_le_centralizer hv
  rwa [piGen_conj] at this

theorem Cfg'.B_ne (h : Cfg' Ω K π z g) :
    conjSub g '' betaOf (nbrAdj Ω) Ω π ≠ π := by
  intro hBπ
  have hcomm : ∀ J ∈ π, ∀ M ∈ π, Commutes J (conjSub g M) := by
    intro J hJ M hM
    rw [← hBπ] at hJ
    obtain ⟨v, hv, rfl⟩ := hJ
    exact (h.std.commutes_of_nbrAdj (hv.2 M hM)).conjSub g
  have hJY : ∀ J ∈ π, J ≤ Subgroup.centralizer (conjSub g (piGen π) : Set G) := by
    intro J hJ x hx y hy
    have hc := commutes_piGen_of (v := J) (π := conjSub g '' π) (by
      rintro _ ⟨M, hM, rfl⟩
      exact hcomm J hJ M hM)
    rw [piGen_conj] at hc
    exact (hc x hx y hy).symm
  have hXY : piGen π ≤ Subgroup.centralizer (conjSub g (piGen π) : Set G) :=
    piGen_le hJY
  have hYX : conjSub g (piGen π) ≤ Subgroup.centralizer (piGen π : Set G) := by
    intro y hy x hx
    exact (Subgroup.mem_centralizer_iff.mp (hXY hx) y hy).symm
  have hMY : ∀ M ∈ conjSub g '' π, M ≤ conjSub g (piGen π) := by
    rintro _ ⟨M', hM', rfl⟩
    exact conjSub_mono (le_piGen hM')
  have hYn : ∀ a : G, a ∈ Subgroup.normalizer (conjSub g (piGen π) : Set G) := by
    intro a
    have : (⨆ M ∈ π ∪ conjSub g '' π, M) ≤ Subgroup.normalizer (conjSub g (piGen π) : Set G) := by
      refine iSup₂_le fun M hM => ?_
      rcases hM with hM | hM
      · exact (le_piGen hM).trans (hXY.trans (Subgroup.centralizer_le_normalizer _))
      · exact (hMY M hM).trans Subgroup.le_normalizer
    rw [h.generate] at this
    exact this (Subgroup.mem_top a)
  have hRY : conjSub g K ≤ conjSub g (piGen π) := by
    have h1 : conjSub g K ≤ conjSub g (conjSub g (piGen π)) :=
      conjSub_mono (h.std.le_conj_piGen h.max h.conj)
    have h2 : conjSub g (conjSub g (piGen π)) = conjSub g (piGen π) := by
      ext x
      rw [mem_conjSub_iff]
      have := (Subgroup.mem_normalizer_iff.mp (hYn g⁻¹) x)
      simpa using this.symm
    rwa [h2] at h1
  have htX : g * z * g⁻¹ ∈ piGen π := h.R_le h.R_inv.mem
  have htY : g * z * g⁻¹ ∈ conjSub g (piGen π) := hRY h.R_inv.mem
  have hcen : g * z * g⁻¹ ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro a
    have : (⨆ M ∈ π ∪ conjSub g '' π, M) ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
      refine iSup₂_le fun M hM => ?_
      rcases hM with hM | hM
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hXY (le_piGen hM hx)) _ htY).symm
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hYX (hMY M hM hx)) _ htX).symm
    rw [h.generate] at this
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this (Subgroup.mem_top a)))
  rw [h.center, Subgroup.mem_bot] at hcen
  exact h.R_inv.ne_one hcen

theorem Cfg'.B_block (h : Cfg' Ω K π z g) :
    ∀ x ∈ piGen π, conjSub x '' (conjSub g '' betaOf (nbrAdj Ω) Ω π) =
        conjSub g '' betaOf (nbrAdj Ω) Ω π ∨
      Disjoint (conjSub x '' (conjSub g '' betaOf (nbrAdj Ω) Ω π))
        (conjSub g '' betaOf (nbrAdj Ω) Ω π) := by
  intro x _
  have e : conjSub x '' (conjSub g '' betaOf (nbrAdj Ω) Ω π) =
      conjSub g '' (conjSub (g⁻¹ * x * g) '' betaOf (nbrAdj Ω) Ω π) := by
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun J _ => ?_
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  rw [e]
  rcases block_betaOf h.std.graph h.mem h.max (g⁻¹ * x * g) with h1 | h1
  · left
    rw [h1]
  · right
    exact (Set.disjoint_image_iff (CFSG.ClassicalInvolution.Generic.conjSub_injective g)).mpr h1

theorem normalizer_conj_back {X : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (conjSub g X : Set G)) :
    g⁻¹ * s * g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.mp hs (g * y * g⁻¹)
  have e1 : g * y * g⁻¹ ∈ (conjSub g X : Set G) ↔ y ∈ X := by
    show g * y * g⁻¹ ∈ conjSub g X ↔ y ∈ X
    rw [mem_conjSub_iff]
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [this]
  have e2 : s * (g * y * g⁻¹) * s⁻¹ ∈ (conjSub g X : Set G) ↔
      g⁻¹ * s * g * y * (g⁻¹ * s * g)⁻¹ ∈ X := by
    show s * (g * y * g⁻¹) * s⁻¹ ∈ conjSub g X ↔ _
    rw [mem_conjSub_iff]
    have : g⁻¹ * (s * (g * y * g⁻¹) * s⁻¹) * g = g⁻¹ * s * g * y * (g⁻¹ * s * g)⁻¹ := by group
    rw [this]
  rw [← e2, ← e1]
  exact h1

@[expose] def sandN (π : Set (Subgroup G)) (z g : G) : Subgroup G :=
  piGen π ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G) ⊓
    Subgroup.centralizer (conjSub g (piGen π) : Set G)

theorem Cfg'.memberData (h : Cfg' Ω K π z g) (hQ : QuasiE4 (piGen π)) :
    MemberData (piGen π) (conjSub g K) (g * z * g⁻¹) := by
  have hR := h.R_inv
  have hRΩ := h.R_mem
  refine ⟨hQ, h.R_le, ⟨(conjSubEquiv K g).symm.trans h.q8.some⟩, hR,
    fun hc => h.h1 _ h.conj _ hR hc, ?_, ?_⟩
  · refine ⟨TwinSecXg.twinJoin Ω (conjSub g K) ⊓ piGen π, ?_, ?_, ?_, ?_⟩
    · exact fun p hp => ⟨hp.2, TwinSecXg.twinJoin_le_centralizer hR hp.1⟩
    · intro s hs p hp
      exact ⟨TwinSecXg.twinJoin_normalized h.std.hyp hR s hs.2 p hp.1,
        (piGen π).mul_mem ((piGen π).mul_mem hs.1 hp.2) ((piGen π).inv_mem hs.1)⟩
    · exact (TwinSecXg.twinJoin_isPGroup h.std.hyp h.std.two hR).to_le inf_le_left
    · exact le_inf (TwinSecXg.le_twinJoin ⟨hRΩ, _, hR, hR⟩) h.R_le
  · intro s hs
    by_cases he : conjSub s (conjSub g K) = conjSub g K
    · exact Or.inl he
    · right
      have hsc : s * (g * z * g⁻¹) * s⁻¹ = g * z * g⁻¹ := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hs.2
        rw [this, mul_inv_cancel_right]
      have hRs : IsUniqueInvolution (conjSub s (conjSub g K)) (g * z * g⁻¹) := by
        have := hR.conj s
        rwa [hsc] at this
      have hΩ : conjSub s (conjSub g K) ∈ Ω := h.std.graph.conjMem _ hRΩ s
      have hne : conjSub g K ≠ conjSub s (conjSub g K) := fun e => he e.symm
      exact commutes_of_mutual_normalizer h.std.hyp h.std.two hRΩ hΩ hne
        (Sec6Gen.le_normalizer_of_twin h.std.hyp hRΩ hΩ hne hR hRs)
        (Sec6Gen.le_normalizer_of_twin h.std.hyp hΩ hRΩ hne.symm hRs hR)

theorem Cfg'.T_le_normalizer (h : Cfg' Ω K π z g) {s : G}
    (hs : s ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :
    s ∈ Subgroup.normalizer (conjSub g (piGen π) : Set G) :=
  (h.std.conj_piGen_le_centralizer h.mem h.max h.h1 h.inv g).2 hs

theorem Cfg'.sandwichData (h : Cfg' Ω K π z g) :
    SandwichData (piGen π) (conjSub g K) (g * z * g⁻¹) (conjSub g '' betaOf (nbrAdj Ω) Ω π)
      (sandN π z g) := by
  have hR := h.R_inv
  have hRΩ := h.R_mem
  have hxo := h.xOrbit_eq
  have hbs := conj_betaOf_subset h.std.graph h.mem h.max h.conj (g := g) rfl
  have hY : ∀ s ∈ piGen π ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G),
      ∀ y ∈ conjSub g (piGen π), s⁻¹ * y * s ∈ conjSub g (piGen π) := by
    intro s hs y hy
    have hn := Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (conjSub g (piGen π) : Set G)).inv_mem (h.T_le_normalizer hs.2)) y
    have := hn.mp hy
    simpa using this
  have hNmem : ∀ n : G, n ∈ sandN π z g ↔ (n ∈ piGen π ∧ n ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) ∧
      n ∈ Subgroup.centralizer (conjSub g (piGen π) : Set G) := fun n => Iff.rfl
  refine ⟨hbs.1, ?_, h.B_block, ?_, fun s hs => h.twin_mem_B hs, inf_le_left, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxo]; exact hbs.2
  · rw [hxo]; exact h.B_ne
  ·
    refine ⟨fun n hn s => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' := (hNmem n).mp hn
    refine (hNmem _).mpr ⟨(s * n * s⁻¹ : ↥(piGen π ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G))).2, ?_⟩
    intro y hy
    have hsy := hY s s.2 y hy
    have hc := Subgroup.mem_centralizer_iff.mp hn'.2 _ hsy
    show y * ((s : G) * n * (s : G)⁻¹) = ((s : G) * n * (s : G)⁻¹) * y
    calc y * ((s : G) * n * (s : G)⁻¹)
        = (s : G) * (((s : G)⁻¹ * y * (s : G)) * n) * (s : G)⁻¹ := by group
      _ = (s : G) * (n * ((s : G)⁻¹ * y * (s : G))) * (s : G)⁻¹ := by rw [hc]
      _ = ((s : G) * n * (s : G)⁻¹) * y := by group
  ·
    refine (hNmem _).mpr ⟨⟨h.R_le hR.mem, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, ?_⟩
    exact (h.std.conj_le_inf_centralizer h.max h.conj hR.mem).2
  ·
    intro s hs x hx
    have hsc : s * (g * z * g⁻¹) * s⁻¹ = g * z * g⁻¹ := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hs.2
      rw [this, mul_inv_cancel_right]
    have hRs : IsUniqueInvolution (conjSub s (conjSub g K)) (g * z * g⁻¹) := by
      have := hR.conj s
      rwa [hsc] at this
    refine (hNmem x).mpr ⟨⟨conjSub_le_of_le_of_mem_left h.R_le hs.1 hx,
      le_centralizer_of_unique hRs hx⟩, ?_⟩
    exact h.B_le_centralizer (h.twin_mem_B hs) hx
  ·
    intro x hx hxN
    have hJ : conjSub x (conjSub g K) ∈ π := by
      rw [← hxo]; exact ⟨x, hx, rfl⟩
    have hJΩ : conjSub x (conjSub g K) ∈ Ω := h.std.graph.conjMem _ hRΩ x
    have hJi : IsUniqueInvolution (conjSub x (conjSub g K)) (x * (g * z * g⁻¹) * x⁻¹) := hR.conj x
    refine ⟨conjSub x (conjSub g K), ?_, hJi⟩
    have hc : ∀ y ∈ piGen (conjSub g '' π), y * (x * (g * z * g⁻¹) * x⁻¹) =
        (x * (g * z * g⁻¹) * x⁻¹) * y := by
      intro y hy
      rw [← Y_eq] at hy
      exact (Subgroup.mem_centralizer_iff.mp ((hNmem _).mp hxN).2 y hy)
    have := h.swap.std.mem_beta_of_centralizes h.swap.max h.swap.h1 hJΩ hJi hc
    rw [← h.beta_conj] at this
    exact this
  ·
    obtain ⟨x₀, hx₀, hx₀e⟩ : conjSub g⁻¹ K ∈ xOrbit (piGen π) (conjSub g K) := by
      rw [hxo]; exact h.conj_inv_mem
    have hab : conjSub (x₀ * g) K = conjSub g⁻¹ K := by
      rw [conjSub_mul]; exact hx₀e
    have hBeq := h.translate_eq hab
    refine relIndex_le_card_fixSet (piGen π) _ _ _ (x₀⁻¹ * g⁻¹) ?_ ?_ ?_
    · intro s hs
      have hn := normalizer_conj_back (h.T_le_normalizer hs.2)
      have e : (x₀⁻¹ * g⁻¹) * s * (x₀⁻¹ * g⁻¹)⁻¹ = x₀⁻¹ * (g⁻¹ * s * g) * x₀ := by group
      rw [e]
      have hx : x₀ ∈ Subgroup.normalizer (piGen π : Set G) := Subgroup.le_normalizer hx₀
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hn) hx
    · intro s hs
      rw [hNmem]
      constructor
      · rintro ⟨-, hsY⟩ y hy
        have hu : g * (x₀ * y * x₀⁻¹) * g⁻¹ ∈ conjSub g (piGen π) :=
          conj_mem_conjSub ((piGen π).mul_mem ((piGen π).mul_mem hx₀ hy) ((piGen π).inv_mem hx₀))
        have hc := Subgroup.mem_centralizer_iff.mp hsY _ hu
        have e1 : (x₀⁻¹ * g⁻¹) * s * (x₀⁻¹ * g⁻¹)⁻¹ * y =
            (x₀⁻¹ * g⁻¹) * (s * (g * (x₀ * y * x₀⁻¹) * g⁻¹)) * (x₀⁻¹ * g⁻¹)⁻¹ := by group
        have e2 : y * ((x₀⁻¹ * g⁻¹) * s * (x₀⁻¹ * g⁻¹)⁻¹) =
            (x₀⁻¹ * g⁻¹) * ((g * (x₀ * y * x₀⁻¹) * g⁻¹) * s) * (x₀⁻¹ * g⁻¹)⁻¹ := by group
        rw [e1, e2, hc]
      · intro H
        refine ⟨⟨hs.1, hs.2⟩, ?_⟩
        intro y' hy'
        have hy := mem_conjSub_iff.mp (show y' ∈ conjSub g (piGen π) from hy')
        have hy₂ : x₀⁻¹ * (g⁻¹ * y' * g) * x₀ ∈ piGen π :=
          (piGen π).mul_mem ((piGen π).mul_mem ((piGen π).inv_mem hx₀) hy) hx₀
        have H2 := H _ hy₂
        have e1 : y' * s = (x₀⁻¹ * g⁻¹)⁻¹ * ((x₀⁻¹ * (g⁻¹ * y' * g) * x₀) *
            ((x₀⁻¹ * g⁻¹) * s * (x₀⁻¹ * g⁻¹)⁻¹)) * (x₀⁻¹ * g⁻¹) := by group
        have e2 : s * y' = (x₀⁻¹ * g⁻¹)⁻¹ * (((x₀⁻¹ * g⁻¹) * s * (x₀⁻¹ * g⁻¹)⁻¹) *
            (x₀⁻¹ * (g⁻¹ * y' * g) * x₀)) * (x₀⁻¹ * g⁻¹) := by group
        rw [e1, e2, H2]
    · intro s hs b hb y hy
      obtain ⟨v, hv, rfl⟩ := hb
      have hb' : conjSub x₀ (conjSub g v) ∈ conjSub x₀ '' (conjSub g '' betaOf (nbrAdj Ω) Ω π) :=
        ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have himg : conjSub x₀ '' (conjSub g '' betaOf (nbrAdj Ω) Ω π) =
          conjSub (x₀ * g) '' betaOf (nbrAdj Ω) Ω π := by
        rw [Set.image_image]
        refine Set.image_congr fun J _ => ?_
        rw [conjSub_mul]
      rw [himg, hBeq] at hb'
      obtain ⟨v', hv', hv'e⟩ := hb'
      have hyb : x₀ * (y : G) * x₀⁻¹ ∈ conjSub x₀ (conjSub g v) := conj_mem_conjSub hy
      rw [← hv'e, mem_conjSub_iff] at hyb
      have hu : g * (x₀ * (y : G) * x₀⁻¹) * g⁻¹ ∈ v' := by simpa using hyb
      have hcv := Subgroup.mem_centralizer_iff.mp (h.std.beta_le_centralizer hv' hu) s hs.1
      have e : (x₀⁻¹ * g⁻¹) * s * (x₀⁻¹ * g⁻¹)⁻¹ * (y : G) * ((x₀⁻¹ * g⁻¹) * s * (x₀⁻¹ * g⁻¹)⁻¹)⁻¹ =
          (x₀⁻¹ * g⁻¹) * (s * (g * (x₀ * (y : G) * x₀⁻¹) * g⁻¹) * s⁻¹) * (x₀⁻¹ * g⁻¹)⁻¹ := by group
      rw [e, hcv, mul_inv_cancel_right]
      group


end Config

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
