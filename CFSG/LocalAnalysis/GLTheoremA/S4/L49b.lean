module

public import CFSG.LocalAnalysis.GLTheoremA.S4.StepTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem l49b_comm_inv {S : Set G} {g : G} (hg : ∀ s ∈ S, s * g = g * s) :
    ∀ s ∈ S, s * g⁻¹ = g⁻¹ * s := by
  intro s hs
  calc s * g⁻¹ = g⁻¹ * (g * s) * g⁻¹ := by group
    _ = g⁻¹ * (s * g) * g⁻¹ := by rw [hg s hs]
    _ = g⁻¹ * s := by group

private theorem l49b_comm_conj {S : Set G} {g y : G} (hg : ∀ s ∈ S, s * g = g * s)
    (hy : ∀ s ∈ S, s * y = y * s) : ∀ s ∈ S, s * (g * y * g⁻¹) = g * y * g⁻¹ * s := by
  intro s hs
  have h1 := l49b_comm_inv hg s hs
  calc s * (g * y * g⁻¹) = (s * g) * y * g⁻¹ := by group
    _ = (g * s) * y * g⁻¹ := by rw [hg s hs]
    _ = g * (s * y) * g⁻¹ := by group
    _ = g * (y * s) * g⁻¹ := by rw [hy s hs]
    _ = g * y * (s * g⁻¹) := by group
    _ = g * y * (g⁻¹ * s) := by rw [h1]
    _ = g * y * g⁻¹ * s := by group

private theorem l49b_normalizer_centralizer {S : Set G} {c : G}
    (hc : c ∈ Subgroup.centralizer S) :
    c ∈ Subgroup.normalizer (Subgroup.centralizer S : Set G) := by
  have hcS : ∀ s ∈ S, s * c = c * s := fun s hs => Subgroup.mem_centralizer_iff.1 hc s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  refine ⟨fun hx => l49b_comm_conj hcS hx, fun hx => ?_⟩
  have h := l49b_comm_conj (l49b_comm_inv hcS) hx
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h

private theorem l49b_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hA hB ⊢
  rw [gLBConj_inf, hA, hB]

private theorem l49b_centralizer_coe_sup (F Z : Subgroup G) :
    Subgroup.centralizer ((F ⊔ Z : Subgroup G) : Set G) =
      Subgroup.centralizer (F : Set G) ⊓ Subgroup.centralizer (Z : Set G) := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    exact ⟨fun f hf => hx f (Subgroup.mem_sup_left hf),
      fun z hz => hx z (Subgroup.mem_sup_right hz)⟩
  · rintro ⟨h1, h2⟩ g hg
    have hle : F ⊔ Z ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le (fun f hf => Subgroup.mem_centralizer_singleton_iff.2 (h1 f hf))
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.2 (h2 z hz))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

private theorem l49b_le_glaPPrimeCoreOf {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p K := by
  haveI hn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hle : N.subgroupOf K ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hn, hcard ▸ hcop⟩
  intro n hn'
  exact ⟨⟨n, hNK hn'⟩, hle hn', rfl⟩

private theorem l49b_glaPComponent_ne_bot {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) :
    L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem glaPLayer_inf_centralizer_sup_ne_bot {p : ℕ} (hp : p.Prime) {C L A F Z : Subgroup G}
    (hL : GLAPComponent p C L) (hAC : A ≤ C) (hZC : Z ≤ C) (hZp : IsPGroup p Z)
    (hZA : ∀ a ∈ A, ∀ c ∈ Z, a * c = c * a) (hZF : ∀ f ∈ F, ∀ c ∈ Z, f * c = c * f)
    (hZL : Z ≤ centModSubgroup p L)
    (hne : GLAPLayer p (closureIn L A ⊓ Subgroup.centralizer (F : Set G)) ≠ ⊥) :
    GLAPLayer p (closureIn L A ⊓ Subgroup.centralizer ((F ⊔ Z : Subgroup G) : Set G)) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := closureIn L A with hH
  set O : Subgroup G := GLAPPrimeCoreOf p C with hO
  set X : Subgroup G := H ⊓ Subgroup.centralizer (F : Set G) with hX
  have hXH : X ≤ H := inf_le_left
  have hHC : H ≤ C := by
    rw [hH, closureIn_eq_iSup_gLBConj]
    refine iSup₂_le fun a ha => ?_
    intro y hy
    have hy' : a * y * a⁻¹ ∈ L := mem_gLBConj.1 hy
    have haC : a ∈ C := hAC ha
    have h1 : a⁻¹ * (a * y * a⁻¹) * a ∈ C :=
      C.mul_mem (C.mul_mem (C.inv_mem haC) (hL.1 hy')) haC
    rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h1
  have hXC : X ≤ C := hXH.trans hHC
  have hZcomm : ∀ c ∈ Z, c ∈ Subgroup.normalizer (H : Set G) ∧ ∀ h ∈ H ⊔ O, ⁅h, c⁆ ∈ O :=
    fun c hc => commutator_mem_of_centMod_closureIn hp hL (hZC hc) hAC
      (fun a ha => hZA a ha c hc) (centMod_iff.2 (hZL hc))
  have hZX : ∀ c ∈ Z, c ∈ Subgroup.normalizer (X : Set G) := by
    intro c hc
    have hcC : c ∈ Subgroup.centralizer (F : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun f hf => hZF f hf c hc
    rw [hX, mem_normalizer_iff_gLBConj_eq, gLBConj_inf,
      mem_normalizer_iff_gLBConj_eq.1 (hZcomm c hc).1,
      mem_normalizer_iff_gLBConj_eq.1 (l49b_normalizer_centralizer hcC)]
  have hcop : ∀ K : Subgroup G, Nat.Coprime p (Nat.card ↥(O ⊓ K)) := fun K => by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    exact not_dvd_card_glaPPrimeCoreOf hp C
      (h.trans (Subgroup.card_dvd_of_le (inf_le_left : O ⊓ K ≤ O)))
  have hXN : X ≤ Subgroup.normalizer ((O ⊓ X : Subgroup G) : Set G) := fun x hx =>
    l49b_normalizer_inf (le_normalizer_glaPPrimeCoreOf p C (hXC hx)) (Subgroup.le_normalizer hx)
  have hOX : O ⊓ X ≤ GLAPPrimeCoreOf p X :=
    l49b_le_glaPPrimeCoreOf (inf_le_right : O ⊓ X ≤ X) hXN (hcop X)
  obtain ⟨D₀, hD₀⟩ : ∃ D₀ : Subgroup G, GLAPComponent p X D₀ := by
    by_contra hcon
    apply hne
    have hempty : {L' : Subgroup G | GLAPComponent p X L'} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun L' hL' => hcon ⟨L', hL'⟩
    unfold GLAPLayer
    rw [hempty, sSup_empty]
  have hD₀X : D₀ ≤ X := hD₀.1
  have hD₀H : D₀ ≤ H := hD₀X.trans hXH
  have hGc : ∀ c ∈ Z, GLBConj c D₀ = D₀ := by
    intro c hc
    have hcX : c ∈ Subgroup.normalizer (X : Set G) := hZX c hc
    have hcomp : GLAPComponent p X (GLBConj c D₀) := by
      have h := glaPComponent_gLBConj hD₀ c
      rwa [mem_normalizer_iff_gLBConj_eq.1 hcX] at h
    have hle : GLBConj c D₀ ≤ D₀ ⊔ GLAPPrimeCoreOf p X := by
      intro y hy
      have hd : c * y * c⁻¹ ∈ D₀ := mem_gLBConj.1 hy
      obtain ⟨d, hdD, hyd⟩ : ∃ d ∈ D₀, y = d * ⁅d⁻¹, c⁻¹⁆ :=
        ⟨c * y * c⁻¹, hd, by simp only [commutatorElement_def]; group⟩
      have hdH : d⁻¹ ∈ H := H.inv_mem (hD₀H hdD)
      have hcd : c⁻¹ * d * c⁻¹⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hcX) d).1 (hD₀X hdD)
      have hcomm_X : ⁅d⁻¹, c⁻¹⁆ ∈ X := by
        have e : ⁅d⁻¹, c⁻¹⁆ = d⁻¹ * (c⁻¹ * d * c⁻¹⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact X.mul_mem (X.inv_mem (hD₀X hdD)) hcd
      have hdO : ⁅d⁻¹, c⁻¹⁆ ∈ O :=
        (hZcomm c⁻¹ (Z.inv_mem hc)).2 d⁻¹ (Subgroup.mem_sup_left hdH)
      rw [hyd]
      exact Subgroup.mul_mem_sup hdD (hOX (Subgroup.mem_inf.2 ⟨hdO, hcomm_X⟩))
    have hmem : GLBConj c D₀ ∈ ({D₀} : Set (Subgroup G)) :=
      mem_of_le_sSup_sup_glaPComponent hp ({D₀} : Set (Subgroup G))
        (fun L' hL' => by rw [Set.mem_singleton_iff.1 hL']; exact hD₀) hcomp
        (by rw [sSup_singleton]; exact hle)
    exact Set.mem_singleton_iff.1 hmem
  have hZD₀ : Z ≤ centModSubgroup p D₀ := by
    intro c hc
    have hcN : c ∈ Subgroup.normalizer (D₀ : Set G) :=
      mem_normalizer_iff_gLBConj_eq.2 (hGc c hc)
    refine mem_centModSubgroup.2 ⟨hcN, fun d hd => ?_⟩
    have hdO : ⁅d, c⁆ ∈ O := (hZcomm c hc).2 d (Subgroup.mem_sup_left (hD₀H hd))
    have hdD : ⁅d, c⁆ ∈ D₀ := by
      have e : ⁅d, c⁆ = d * (c * d⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact D₀.mul_mem hd ((Subgroup.mem_normalizer_iff.1 hcN d⁻¹).1 (D₀.inv_mem hd))
    have hD₀N : D₀ ≤ Subgroup.normalizer ((O ⊓ D₀ : Subgroup G) : Set G) := fun x hx =>
      l49b_normalizer_inf (le_normalizer_glaPPrimeCoreOf p C (hXC (hD₀X hx)))
        (Subgroup.le_normalizer hx)
    exact l49b_le_glaPPrimeCoreOf (inf_le_right : O ⊓ D₀ ≤ D₀) hD₀N (hcop D₀)
      (Subgroup.mem_inf.2 ⟨hdO, hdD⟩)
  obtain ⟨hD₁, -, -, -, -⟩ := glaPLayer_inf_centralizer_of_isPGroup hp hD₀ hZp hZD₀
  have hsub : IsSubnormal (D₀ ⊓ Subgroup.centralizer (Z : Set G))
      (X ⊓ Subgroup.centralizer (Z : Set G)) := hD₀.2.1.inf _
  have hD₁X : GLAPComponent p (X ⊓ Subgroup.centralizer (Z : Set G))
      (GLAPLayer p (D₀ ⊓ Subgroup.centralizer (Z : Set G))) :=
    glaPComponent_of_isSubnormal' hp hsub hD₁
  have hD₁ne : GLAPLayer p (D₀ ⊓ Subgroup.centralizer (Z : Set G)) ≠ ⊥ :=
    l49b_glaPComponent_ne_bot hD₁
  have hXZ : GLAPLayer p (X ⊓ Subgroup.centralizer (Z : Set G)) ≠ ⊥ := by
    intro hbot
    apply hD₁ne
    have hle : GLAPLayer p (D₀ ⊓ Subgroup.centralizer (Z : Set G)) ≤
        GLAPLayer p (X ⊓ Subgroup.centralizer (Z : Set G)) :=
      le_sSup (s := {L' | GLAPComponent p (X ⊓ Subgroup.centralizer (Z : Set G)) L'}) hD₁X
    rw [hbot] at hle
    exact le_bot_iff.1 hle
  have hcent : H ⊓ Subgroup.centralizer ((F ⊔ Z : Subgroup G) : Set G) =
      X ⊓ Subgroup.centralizer (Z : Set G) := by
    rw [hX, l49b_centralizer_coe_sup, ← inf_assoc]
  rw [hcent]
  exact hXZ

private theorem l49b_card_arith {e a z b b' v s f m u : ℕ}
    (eq1 : b' * v = a * z) (eq2 : m * u = f * z) (eq3 : s * f = e * a) (le1 : s ≤ b)
    (le2 : u ≤ v) (hb : b = b') (hbpos : 0 < b) (hvpos : 0 < v) : e ≤ m := by
  have hbv : b * v = a * z := by rw [hb]; exact eq1
  have key : e * (a * z) ≤ b * (m * v) := by
    calc e * (a * z) = (e * a) * z := by ring
      _ = (s * f) * z := by rw [eq3]
      _ ≤ (b * f) * z := Nat.mul_le_mul (Nat.mul_le_mul le1 le_rfl) le_rfl
      _ = b * (f * z) := by ring
      _ = b * (m * u) := by rw [eq2]
      _ ≤ b * (m * v) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl le2)
  have h1 : e * (b * v) ≤ m * (b * v) := by
    calc e * (b * v) = e * (a * z) := by rw [hbv]
      _ ≤ b * (m * v) := key
      _ = m * (b * v) := by ring
  exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos hbpos hvpos)

theorem card_le_card_inf_sup {p : ℕ} {B B' L E : Subgroup G} (hB : IsElemAbelian p B)
    (hB' : IsElemAbelian p B') (hcard : Nat.card B = Nat.card B')
    (hdec : ∀ b ∈ B', ∃ u ∈ B ⊓ B', ∃ v ∈ B', CentMod p L v ∧ b = u * v) (hEB : E ≤ B) :
    Nat.card E ≤ Nat.card ((E ⊓ (B ⊓ B')) ⊔ (B' ⊓ centModSubgroup p L) : Subgroup G) := by
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    isElemAbelian_commute hB hx hy
  have hcommB' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := fun x hx y hy =>
    isElemAbelian_commute hB' hx hy
  set A : Subgroup G := B ⊓ B' with hA
  set Z : Subgroup G := B' ⊓ centModSubgroup p L with hZ
  set F₀ : Subgroup G := E ⊓ A with hF₀
  have hAB : A ≤ B := (inf_le_left : B ⊓ B' ≤ B)
  have hAB' : A ≤ B' := (inf_le_right : B ⊓ B' ≤ B')
  have hZB' : Z ≤ B' := (inf_le_left : B' ⊓ centModSubgroup p L ≤ B')
  have hF₀A : F₀ ≤ A := (inf_le_right : E ⊓ A ≤ A)
  have hZN : Z ≤ Subgroup.normalizer (A : Set G) := fun z hz =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun a ha => hcommB' a (hAB' ha) z (hZB' hz))
  have hZN₀ : Z ≤ Subgroup.normalizer (F₀ : Set G) := fun z hz =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun f hf => hcommB' f (hAB' (hF₀A hf)) z (hZB' hz))
  have hAN : A ≤ Subgroup.normalizer (E : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun e he => hcommB e (hEB he) a (hAB ha))
  have hBAZ : A ⊔ Z = B' := by
    refine le_antisymm (sup_le hAB' hZB') ?_
    intro b hb
    obtain ⟨u, hu, v, hv, hvL, rfl⟩ := hdec b hb
    exact Subgroup.mul_mem_sup hu (Subgroup.mem_inf.2 ⟨hv, centMod_iff.1 hvL⟩)
  have eq1 : Nat.card B' * Nat.card (A ⊓ Z : Subgroup G) = Nat.card A * Nat.card Z := by
    have h := card_sup_mul_card_inf_of_le_normalizer hZN
    rwa [hBAZ] at h
  have eq2 : Nat.card (F₀ ⊔ Z : Subgroup G) * Nat.card (F₀ ⊓ Z : Subgroup G) =
      Nat.card F₀ * Nat.card Z :=
    card_sup_mul_card_inf_of_le_normalizer hZN₀
  have eq3 : Nat.card (E ⊔ A : Subgroup G) * Nat.card F₀ = Nat.card E * Nat.card A :=
    card_sup_mul_card_inf_of_le_normalizer hAN
  have le1 : Nat.card (E ⊔ A : Subgroup G) ≤ Nat.card B :=
    Subgroup.card_le_of_le (sup_le hEB hAB)
  have le2 : Nat.card (F₀ ⊓ Z : Subgroup G) ≤ Nat.card (A ⊓ Z : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_right Z hF₀A)
  exact l49b_card_arith eq1 eq2 eq3 le1 le2 hcard (Nat.card_pos (α := B))
    (Nat.card_pos (α := (A ⊓ Z : Subgroup G)))

theorem exists_le_card_eq_pow {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p P)
    {n : ℕ} (h : p ^ n ≤ Nat.card P) : ∃ F : Subgroup G, F ≤ P ∧ Nat.card F = p ^ n := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hnk : n ≤ k := by
    rw [hk] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  have hdvd : p ^ n ∣ Nat.card P := by
    rw [hk]
    exact Nat.pow_dvd_pow p hnk
  obtain ⟨K, hK, -, hKP⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (H := ⊥) (L := P)
    (by simp) hdvd bot_le
  exact ⟨K, hKP, hK⟩

end CFSG.LocalAnalysis.GLTheoremA
