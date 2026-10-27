module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269B3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Gen

variable {G : Type} [Group G]

theorem E3.mem_closure_pair_cases {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {p : G} (hp : p ∈ Subgroup.closure ({a, b} : Set G)) :
    p = 1 ∨ p = a ∨ p = b ∨ p = a * b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have hSa : ∀ y : G, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (a * y = 1 ∨ a * y = a ∨ a * y = b ∨ a * y = a * b) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one a))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, ha, one_mul])))
  have hSb : ∀ y : G, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (b * y = 1 ∨ b * y = a ∨ b * y = b ∨ b * y = a * b) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl (mul_one b)))
    · exact Or.inr (Or.inr (Or.inr hab.symm))
    · exact Or.inl hb
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]))
  induction hp using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left x hx y _ hy =>
    rcases hx with rfl | rfl
    · exact hSa y hy
    · exact hSb y hy
  | inv_mul_cancel x hx y _ hy =>
    rcases hx with rfl | rfl
    · rw [hainv]
      exact hSa y hy
    · rw [hbinv]
      exact hSb y hy

theorem E3.oddCore_le_centralizer_of_alpha_mem {A : Subgroup G} (hα : alphaOf A = ⊥) {w v : G}
    (hw : w ∈ A) (hw1 : w ≠ 1) (hv : v ∈ A) :
    oddCoreOf (Subgroup.centralizer ({w} : Set G)) ≤ Subgroup.centralizer ({v} : Set G) := by
  have h1 : ⁅oddCoreOf (Subgroup.centralizer ({w} : Set G)), A⁆ ≤ alphaOf A :=
    le_sup_of_le_left (le_iSup₂_of_le w hw (le_iSup_of_le hw1 le_rfl))
  rw [hα, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (h1 hy) v hv).symm

theorem E3.eq_of_mem_closure_pair_sup [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {N : Subgroup G} (hN : Odd (Nat.card N))
    (hNa : N ≤ Subgroup.centralizer ({a} : Set G)) (hNb : N ≤ Subgroup.centralizer ({b} : Set G))
    {w : G} (hw : w ∈ Subgroup.closure ({a, b} : Set G) ⊔ N) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    w = a ∨ w = b ∨ w = a * b := by
  set V := Subgroup.closure ({a, b} : Set G) with hVdef
  set C := Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) with hCdef
  have hcen : ∀ g ∈ C, ∀ v ∈ V, v * g = g * v := by
    intro g hg v hv
    have hVle : V ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [hVdef, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hg.1).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hg.2).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hVle hv)
  have hVC : V ≤ C := by
    rw [hVdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
        Subgroup.mem_centralizer_singleton_iff.mpr hab⟩
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hab.symm,
        Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hwC : w ∈ C := sup_le hVC (le_inf hNa hNb) hw
  have hVN : V ≤ Subgroup.normalizer (N : Set G) := by
    intro v hv
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun n hn => ?_)
    exact (hcen n ⟨hNa hn, hNb hn⟩ v hv).symm
  have hw' : w ∈ ((V ⊔ N : Subgroup G) : Set G) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right V N hVN] at hw'
  obtain ⟨v, hv, o, ho, rfl⟩ := hw'
  have hv4 := E3.mem_closure_pair_cases ha hb hab hv
  have hv2 : v * v = 1 := by
    rcases hv4 with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact ha
    · exact hb
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = a * a * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
  have h1 : v * (v * o) = v * o * v := hcen (v * o) hwC v hv
  have h2 : o = v * o * v := by
    calc o = v * v * o := by rw [hv2, one_mul]
      _ = v * (v * o) := by group
      _ = v * o * v := h1
  have hov : o * v = v * o := by
    calc o * v = v * o * v * v := by rw [← h2]
      _ = v * o * (v * v) := by group
      _ = v * o := by rw [hv2, mul_one]
  have ho2 : o * o = 1 := by
    calc o * o = v * v * (o * o) := by rw [hv2, one_mul]
      _ = v * (v * o) * o := by group
      _ = v * (o * v) * o := by rw [hov]
      _ = v * o * (v * o) := by group
      _ = 1 := hw2
  have ho1 : o = 1 := by
    by_contra hne
    exact hne (eq_one_of_isPGroup_of_mem_odd hN ho (isPGroup_zpowers_of_mul_self_eq_one ho2 hne))
  subst ho1
  simp only [mul_one] at hw1 ⊢
  rcases hv4 with rfl | rfl | rfl | rfl
  · exact absurd rfl hw1
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Gen

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.not_cent_of_c264One (hF : E3Frame n R S t J u) {Rd : Subgroup Y}
    (hRd : tightCore Rd = J) (hC1 : C264One (CoreAssembly.conjClass (tightCore Rd)) u t) {x : Y}
    (hx : x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J) :
    ¬ ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
      ⁅x * (u * t) * x⁻¹, y⁆ ∈
        oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) := by
  classical
  intro hb
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set X := nbrGen (TC.nbrAdj Ω) J with hXdef
  set π := orbOf (TC.nbrAdj Ω) (tightCore R) J with hπdef
  set P := E3.orbGen Ω (tightCore R) J with hPdef
  have hd := hF.large.datum
  have hΩG := hd.hypOmegaGen
  have hR : TypeRFam 3 Ω := TightLargeHypR.typeRFam hF.large
  have hcl : ConjInvariant Ω := hΩG.conjInvariant
  have hJn : J ∈ omegaNbr Ω (tightCore R) := hF.maxAdj.1.2
  have hJΩ : J ∈ Ω := hJn.1
  have hK₀Ω : tightCore R ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hK₀J : tightCore R ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩG hF.maxAdj.1.1 hJn.1 hJn
  have hJπ : J ∈ π := mem_orbOf_self _ _
  have hXC : X ≤ Subgroup.centralizer ({u} : Set Y) := hF.nbrGen_le_centralizer
  have hCuJ : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer (J : Set Y) :=
    hR.tight J hJΩ u hF.inv
  have hJC : J ≤ Subgroup.centralizer ({u} : Set Y) := hR.le_centralizer hJΩ hF.inv
  have hu2 : u * u = 1 := hF.inv.sq
  have ht2 : t * t = 1 := hd.isUniqueInvolution_core.sq
  have hut : u * t = t * u := (Subgroup.mem_centralizer_singleton_iff.mp hF.t_mem_centralizer).symm
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hXC hx)
  have htu1 : t ≠ u := by
    intro h
    apply hJn.2.1
    have hJt : IsUniqueInvolution J t := by rw [h]; exact hF.inv
    exact hR.noTwins _ hK₀Ω J ⟨hJΩ, t, hd.isUniqueInvolution_core, hJt⟩
  have ha1 : u * t ≠ 1 := by
    intro h
    apply htu1
    calc t = u * (u * t) := by rw [← mul_assoc, hu2, one_mul]
      _ = u := by rw [h, mul_one]
  have hut2 : u * t * (u * t) = 1 := by
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [← hut]
      _ = u * u * (t * t) := by group
      _ = 1 := by rw [hu2, ht2, one_mul]
  obtain ⟨g, hg'⟩ := hJn.1
  have hgJ : conjSub g (tightCore R) = J := hg'
  have hfamJ : CoreAssembly.conjClass J = Ω := by rw [← hgJ, conjClass_conjSub]
  rw [hRd, hfamJ] at hC1
  have hN : Subgroup.centralizer ({u * t} : Set Y) ≤ Subgroup.normalizer
      ((Subgroup.closure ({u * t, u} : Set Y) ⊔ oddCoreOf (layerY Ω (u * t)) : Subgroup Y) :
        Set Y) := hC1
  have hαut : alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := hF.alpha J hJn u hF.inv
  have hOY : oddCoreOf (layerY Ω (u * t)) ≤ Subgroup.centralizer ({u * t} : Set Y) :=
    (oddCoreOf_le_self _).trans (layerY_le_centralizer (Ω := Ω) (x := u * t))
  have hOYu : oddCoreOf (layerY Ω (u * t)) ≤ Subgroup.centralizer ({u} : Set Y) :=
    (Asc77.T8.oddCoreOf_le_oddCoreOf_of_normalized (layerY_le_centralizer (Ω := Ω) (x := u * t))
      fun c hc => layerY_conjSub_eq hcl hc).trans
      (E3.oddCore_le_centralizer_of_alpha_mem hαut
        (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))) ha1 (Subgroup.subset_closure (by simp)))
  have hπK : ∀ M ∈ π, M ∈ omegaNbr Ω (tightCore R) := fun M hM =>
    (adj_of_mem_isMaxOrb hF.graphFam hF.maxAdj.2 hM).2
  have hPC : P ≤ Subgroup.centralizer ({t} : Set Y) := by
    refine iSup₂_le fun L hL => ?_
    obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hΩG (hπK L hL).1
    exact edge_le_centralizer_of_alpha hd (hπK L hL) hv (hF.alpha L (hπK L hL) v hv)
  have hOPJ : oddCoreOf P ≤ Subgroup.normalizer (J : Set Y) :=
    ((Asc77.T8.oddCoreOf_le_oddCoreOf_of_normalized hPC fun c hc =>
      hF.conjSub_orbGen_core hc).trans
      (E3.oddCore_le_centralizer_of_alpha hαut (ne_one_of_datum hd))).trans hCuJ
  set b := x * (u * t) * x⁻¹ with hbdef
  have hb2 : b * b = 1 := by
    calc b * b = x * (u * t * (u * t)) * x⁻¹ := by rw [hbdef]; group
      _ = 1 := by rw [hut2]; group
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1
    calc u * t = x⁻¹ * b * x := by rw [hbdef]; group
      _ = 1 := by rw [h]; group
  have hbP : ∀ y ∈ P, b * y * b⁻¹ ∈ P := fun y hy => by
    have e : b * y * b⁻¹ = ⁅b, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]
    exact P.mul_mem (oddCoreOf_le_self P (hb y hy)) hy
  have hbN : b ∈ Subgroup.normalizer (P : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hbP h, fun hh => ?_⟩
    have h1 := hbP _ hh
    have e : b * (b * h * b⁻¹) * b⁻¹ = h := by
      calc b * (b * h * b⁻¹) * b⁻¹ = b * b * h * (b * b)⁻¹ := by group
        _ = h := by rw [hb2]; group
    rwa [e] at h1
  have hzb : ∀ c ∈ Subgroup.zpowers b, c = 1 ∨ c = b := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hbsq : b ^ (2 : ℤ) = 1 := by rw [zpow_two, hb2]
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, hbsq, one_zpow]
    · right
      rw [zpow_add, zpow_mul, hbsq, one_zpow, one_mul, zpow_one]
  have hcov : ∀ M ∈ π, ∃ c ∈ Subgroup.centralizer ({b} : Set Y), conjSub c J = M := by
    intro M hM
    obtain ⟨y, hyP, hyM⟩ := hF.lemma1710.trans J hJπ M hM
    obtain ⟨o, ho, hfix⟩ := Balance.Bootstrap.exists_fixed_mem_coset_of_isPGroup
      (isPGroup_zpowers_of_mul_self_eq_one hb2 hb1) (oddCoreOf_odd_natCard P)
      (fun c hc o ho => mem_normalizer_oddCoreOf_of_mem_normalizer
        ((Subgroup.zpowers_le.mpr hbN) hc) ho) (x := y) (fun c hc => by
          rcases hzb c hc with rfl | rfl
          · simp
          · have h1 := mem_normalizer_oddCoreOf_of_mem_normalizer
              (Subgroup.le_normalizer (P.inv_mem hyP)) (hb y hyP)
            convert h1 using 1
            rw [commutatorElement_def]
            group)
    refine ⟨y * o, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hfix b (Subgroup.mem_zpowers b)
      calc y * o * b = b * (y * o) * b⁻¹ * b := by rw [h1]
        _ = b * (y * o) := by group
    · rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp (hOPJ ho), hyM]
  have hJ₁Ω : conjSub x (tightCore R) ∈ Ω := hcl x _ hK₀Ω
  have hJ₁inv : IsUniqueInvolution (conjSub x (tightCore R)) (x * t * x⁻¹) :=
    hd.isUniqueInvolution_core.conj x
  have hK₀X : tightCore R ≤ X :=
    le_iSup₂ (f := fun N (_ : N ∈ {N | TC.nbrAdj Ω J N}) => N) _ ⟨hJΩ, hK₀J⟩
  have hJ₁C : conjSub x (tightCore R) ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have h1 := X.mul_mem (X.mul_mem hx (hK₀X hy)) (X.inv_mem hx)
    exact hXC (by simpa [mul_assoc] using h1)
  have hxu' : x⁻¹ * u * x = u := by
    calc x⁻¹ * u * x = x⁻¹ * (u * x) := by group
      _ = x⁻¹ * (x * u) := by rw [hxu]
      _ = u := by group
  have hπC : ∀ M ∈ π, M ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro M hM
    obtain ⟨c, hcb, hcM⟩ := hcov M hM
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hcb
    have hc' : x⁻¹ * c * x ∈ Subgroup.centralizer ({u * t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x⁻¹ * c * x * (u * t) = x⁻¹ * (c * b) * x := by rw [hbdef]; group
        _ = x⁻¹ * (b * c) * x := by rw [h1]
        _ = u * t * (x⁻¹ * c * x) := by rw [hbdef]; group
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp hc'
    set w := x⁻¹ * c * x * u * (x⁻¹ * c * x)⁻¹ with hwdef
    have hwE : w ∈ Subgroup.closure ({u * t, u} : Set Y) ⊔ oddCoreOf (layerY Ω (u * t)) :=
      (Subgroup.mem_normalizer_iff.mp (hN hc') u).mp
        (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
    have hw2 : w * w = 1 := by
      calc w * w = x⁻¹ * c * x * (u * u) * (x⁻¹ * c * x)⁻¹ := by rw [hwdef]; group
        _ = 1 := by rw [hu2]; group
    have hwu : u = (x⁻¹ * c * x)⁻¹ * w * (x⁻¹ * c * x) := by rw [hwdef]; group
    have hw1 : w ≠ 1 := by
      intro h
      apply hF.inv.ne_one
      rw [hwu, h]
      group
    have hwa : w ≠ u * t := by
      intro h
      apply ne_one_of_datum hd
      have h3 : u = u * t := by
        calc u = (x⁻¹ * c * x)⁻¹ * w * (x⁻¹ * c * x) := hwu
          _ = (x⁻¹ * c * x)⁻¹ * (u * t * (x⁻¹ * c * x)) := by rw [h]; group
          _ = (x⁻¹ * c * x)⁻¹ * (x⁻¹ * c * x * (u * t)) := by rw [← h2]
          _ = u * t := by group
      calc t = u⁻¹ * (u * t) := by group
        _ = 1 := by rw [← h3, inv_mul_cancel]
    have hzM : c * u * c⁻¹ = x * w * x⁻¹ := by
      calc c * u * c⁻¹ = x * (x⁻¹ * c * x) * (x⁻¹ * u * x) * (x⁻¹ * c * x)⁻¹ * x⁻¹ := by group
        _ = x * w * x⁻¹ := by rw [hxu', hwdef]; group
    have hab : u * t * u = u * (u * t) := by rw [mul_assoc, ← hut]
    have hMinv := hF.inv.conj c
    rw [hcM, hzM] at hMinv
    rcases E3.eq_of_mem_closure_pair_sup hut2 hu2 hab (oddCoreOf_odd_natCard _) hOY hOYu hwE hw2
      hw1 with h | h | h
    · exact absurd h hwa
    · have hxux : x * w * x⁻¹ = u := by
        rw [h]
        calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [hxu]
          _ = u := by group
      rw [hxux] at hMinv
      rw [hR.noTwins J hJΩ M ⟨(hπK M hM).1, u, hF.inv, hMinv⟩]
      exact hJC
    · have hwt : x * w * x⁻¹ = x * t * x⁻¹ := by
        rw [h, hab, ← mul_assoc u u t, hu2, one_mul]
      rw [hwt] at hMinv
      rw [hR.noTwins _ hJ₁Ω M ⟨(hπK M hM).1, x * t * x⁻¹, hJ₁inv, hMinv⟩]
      exact hJ₁C
  have hPu : P ≤ Subgroup.centralizer ({u} : Set Y) := iSup₂_le fun M hM => hπC M hM
  have hπJ : ∀ M ∈ π, M = J := by
    intro M hM
    obtain ⟨y, hyP, hyM⟩ := hF.lemma1710.trans J hJπ M hM
    rw [← hyM]
    exact mem_normalizer_iff_conjSub_eq.mp (hCuJ (hPu hyP))
  have hPJ : P = J :=
    le_antisymm (iSup₂_le fun M hM => (hπJ M hM).le) (le_iSup₂_of_le J hJπ le_rfl)
  have hXN : X ≤ Subgroup.normalizer (P : Set Y) := by
    rw [hPJ]
    exact hXC.trans hCuJ
  exact hF.false_of_le_normalizer hXN

theorem tightE3C268Ex_proved {n : ℕ} : TightE3C268Ex n :=
  fun _ _ _ _ _ _ _ _ hF _ _ _ _ _ _ _ _ _ _ _ _ hRd _ _ hC1 _ hx =>
    hF.not_cent_of_c264One hRd hC1 hx

theorem tightE3C269S_of_gen {n : ℕ} (hGen : TightE3C269Gen n) : TightE3C269S n :=
  tightE3C269S_of tightE3C268Ex_proved hGen

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
