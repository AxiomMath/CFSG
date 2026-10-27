module

public import CFSG.LocalAnalysis.GLTheoremA.S6.I183Diag
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt73
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4 Subgroup
open scoped Pointwise commutatorElement

section Generic

variable {Γ : Type} [Group Γ]

theorem i2_triple {C₀ C₁ C₂ : Subgroup Γ} (h01 : ∀ a ∈ C₀, ∀ b ∈ C₁, Commute a b)
    (h02 : ∀ a ∈ C₀, ∀ c ∈ C₂, Commute a c) (h12 : ∀ b ∈ C₁, ∀ c ∈ C₂, Commute b c)
    {g : Γ} (hg : g ∈ C₀ ⊔ C₁ ⊔ C₂) :
    ∃ a ∈ C₀, ∃ b ∈ C₁, ∃ c ∈ C₂, g = a * b * c := by
  let T : Subgroup Γ :=
    { carrier := {x | ∃ a ∈ C₀, ∃ b ∈ C₁, ∃ c ∈ C₂, x = a * b * c}
      one_mem' := ⟨1, C₀.one_mem, 1, C₁.one_mem, 1, C₂.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, c, hc, rfl⟩ ⟨a', ha', b', hb', c', hc', rfl⟩
        refine ⟨a * a', C₀.mul_mem ha ha', b * b', C₁.mul_mem hb hb', c * c', C₂.mul_mem hc hc', ?_⟩
        have e1 : c * a' = a' * c := (h02 a' ha' c hc).symm.eq
        have e2 : b * a' = a' * b := (h01 a' ha' b hb).symm.eq
        have e3 : c * b' = b' * c := (h12 b' hb' c hc).symm.eq
        have e4 : b * c * a' = a' * b * c := by
          rw [mul_assoc, e1, ← mul_assoc, e2]
        calc a * b * c * (a' * b' * c') = a * (b * c * a') * b' * c' := by group
          _ = a * (a' * b * c) * b' * c' := by rw [e4]
          _ = a * a' * (b * (c * b')) * c' := by group
          _ = a * a' * (b * (b' * c)) * c' := by rw [e3]
          _ = a * a' * (b * b') * (c * c') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, c, hc, rfl⟩
        refine ⟨a⁻¹, C₀.inv_mem ha, b⁻¹, C₁.inv_mem hb, c⁻¹, C₂.inv_mem hc, ?_⟩
        have e1 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := (h01 a ha b hb).inv_inv.eq
        have e2 : a⁻¹ * c⁻¹ = c⁻¹ * a⁻¹ := (h02 a ha c hc).inv_inv.eq
        have e3 : b⁻¹ * c⁻¹ = c⁻¹ * b⁻¹ := (h12 b hb c hc).inv_inv.eq
        calc (a * b * c)⁻¹ = c⁻¹ * b⁻¹ * a⁻¹ := by group
          _ = c⁻¹ * (b⁻¹ * a⁻¹) := by group
          _ = c⁻¹ * (a⁻¹ * b⁻¹) := by rw [← e1]
          _ = (c⁻¹ * a⁻¹) * b⁻¹ := by group
          _ = (a⁻¹ * c⁻¹) * b⁻¹ := by rw [← e2]
          _ = a⁻¹ * (c⁻¹ * b⁻¹) := by group
          _ = a⁻¹ * (b⁻¹ * c⁻¹) := by rw [← e3]
          _ = a⁻¹ * b⁻¹ * c⁻¹ := by group }
  have hle : C₀ ⊔ C₁ ⊔ C₂ ≤ T := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      exact ⟨a, ha, 1, C₁.one_mem, 1, C₂.one_mem, by simp⟩
    · intro b hb
      exact ⟨1, C₀.one_mem, b, hb, 1, C₂.one_mem, by simp⟩
    · intro c hc
      exact ⟨1, C₀.one_mem, 1, C₁.one_mem, c, hc, by simp⟩
  exact hle hg

end Generic

section Quotients

variable {Y' : Type} [Group Y']

theorem i2_centralizer_normal {D Kb : Subgroup Y'}
    (hDn : ∀ y ∈ Kb, ∀ d ∈ D, y * d * y⁻¹ ∈ D) :
    Subgroup.Normal (((Subgroup.centralizer (D : Set Y')) ⊓ Kb).subgroupOf Kb) := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨hnC, hnK⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hn)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  refine ⟨?_, Kb.mul_mem (Kb.mul_mem g.2 hnK) (Kb.inv_mem g.2)⟩
  rw [Subgroup.mem_centralizer_iff] at hnC ⊢
  intro d hd
  have hyd : (g : Y')⁻¹ * d * g ∈ D := by
    have := hDn (g : Y')⁻¹ (Kb.inv_mem g.2) d hd
    simpa [mul_assoc] using this
  have hc := hnC _ hyd
  calc d * ((g : Y') * n * (g : Y')⁻¹) = (g : Y') * ((g : Y')⁻¹ * d * g * n) * (g : Y')⁻¹ := by group
    _ = (g : Y') * (n * ((g : Y')⁻¹ * d * g)) * (g : Y')⁻¹ := by rw [hc]
    _ = (g : Y') * n * (g : Y')⁻¹ * d := by group

theorem i2_centralizer_quot_iso {D Kb : Subgroup Y'} (hDKb : D ≤ Kb)
    (hDn : ∀ y ∈ Kb, ∀ d ∈ D, y * d * y⁻¹ ∈ D)
    (hdec : ∀ y ∈ Kb, ∃ a ∈ D, ∃ n ∈ Subgroup.centralizer (D : Set Y'), y = a * n)
    [hN : Subgroup.Normal (((Subgroup.centralizer (D : Set Y')) ⊓ Kb).subgroupOf Kb)] :
    Nonempty (↥Kb ⧸ ((Subgroup.centralizer (D : Set Y')) ⊓ Kb).subgroupOf Kb ≃*
      ↥D ⧸ Subgroup.center ↥D) := by
  classical
  set N : Subgroup Kb := ((Subgroup.centralizer (D : Set Y')) ⊓ Kb).subgroupOf Kb with hNdef
  set H : Subgroup Kb := D.subgroupOf Kb with hHdef
  let f : H →* Kb ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨a, ha, n, hn, hgan⟩ := hdec g.1 g.2
    refine ⟨⟨⟨a, hDKb ha⟩, Subgroup.mem_subgroupOf.2 ha⟩, ?_⟩
    show (QuotientGroup.mk' N ⟨a, hDKb ha⟩ : Kb ⧸ N) = QuotientGroup.mk' N g
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [hNdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hn' : a⁻¹ * g.1 = n := by rw [hgan]; group
    refine ⟨?_, ?_⟩
    · show a⁻¹ * g.1 ∈ Subgroup.centralizer (D : Set Y')
      rw [hn']
      exact hn
    · show a⁻¹ * g.1 ∈ Kb
      exact Kb.mul_mem (Kb.inv_mem (hDKb ha)) g.2
  have hker : f.ker = N.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' N h.1 = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let e1 : H ⧸ f.ker ≃* Kb ⧸ N := QuotientGroup.quotientKerEquivOfSurjective f hsurj
  have hmap : (N.subgroupOf H).map (Subgroup.subgroupOfEquivOfLe hDKb : ↥(D.subgroupOf Kb) ≃* ↥D).toMonoidHom
      = Subgroup.center ↥D := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      have hh' : h ∈ N.subgroupOf H := hh
      rw [Subgroup.mem_subgroupOf, hNdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hh'
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hc := Subgroup.mem_centralizer_iff.1 hh'.1 y.1 y.2
      exact hc
    · intro hx
      have hxC : (x.1 : Y') ∈ Subgroup.centralizer (D : Set Y') :=
        Subgroup.mem_centralizer_iff.2 (fun d hd => congrArg Subtype.val
          (Subgroup.mem_center_iff.1 hx ⟨d, hd⟩))
      have hmemN : (⟨x.1, hDKb x.2⟩ : Kb) ∈ N := by
        rw [hNdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨hxC, hDKb x.2⟩
      refine ⟨⟨⟨x.1, hDKb x.2⟩, Subgroup.mem_subgroupOf.2 x.2⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 hmemN
      · rfl
  exact ⟨e1.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.congr (N.subgroupOf H) (Subgroup.center ↥D)
      (Subgroup.subgroupOfEquivOfLe hDKb : ↥(D.subgroupOf Kb) ≃* ↥D) hmap))⟩

end Quotients

section PSimpleUtil

def i2_centre_quot_congr {P Q : Type} [Group P] [Group Q] (e : P ≃* Q) :
    (P ⧸ Subgroup.center P) ≃* (Q ⧸ Subgroup.center Q) :=
  QuotientGroup.congr (Subgroup.center P) (Subgroup.center Q) e (Subgroup.map_center_eq e)

variable {G : Type} [Group G] [Finite G]

noncomputable def i2_pquot_conj (g : G) (M : Subgroup G) :
    (↥M ⧸ GLAPPrimeCore 3 ↥M) ≃* (↥(GLBConj g M) ⧸ GLAPPrimeCore 3 ↥(GLBConj g M)) :=
  QuotientGroup.congr (GLAPPrimeCore 3 ↥M) (GLAPPrimeCore 3 ↥(GLBConj g M)) (conjEquiv g M)
    (glaPPrimeCore_map_iso 3 (conjEquiv g M))

noncomputable def i2_psimple_conj (g : G) (M : Subgroup G) :
    PSimple 3 M ≃* PSimple 3 (GLBConj g M) :=
  i2_centre_quot_congr (i2_pquot_conj g M)

noncomputable def i2_psimple_barX {X C : Subgroup G} (hC : GLAPComponent 3 X C) :
    PSimple 3 C ≃* (↥(barX 3 X C) ⧸ Subgroup.center ↥(barX 3 X C)) :=
  i2_centre_quot_congr (quotEquivBarX Nat.prime_three hC.1 hC.2.1)

end PSimpleUtil

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem i2_coprime {p : ℕ} (hp : p.Prime) {X K : Subgroup G} {x : G} (hKX : K ≤ X)
    (hxX : x ∈ X) (hx : IsElemAbelian p (Subgroup.zpowers x))
    (hKn : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hKn' : ∀ k ∈ K, x⁻¹ * k * x ∈ K)
    {y : ↥X ⧸ GLAPPrimeCore p ↥X} (hyK : y ∈ barX p X K)
    (hyE : Commute y (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩)) :
    y ∈ barX p X (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := by
    refine Subgroup.mem_normalizer_iff.2 (fun h => ⟨fun hh => hKn h hh, fun hh => ?_⟩)
    have := hKn' _ hh
    simpa [mul_assoc] using this
  set W : Subgroup G := K ⊔ Subgroup.zpowers x with hW
  have hWX : W ≤ X := sup_le hKX (Subgroup.zpowers_le.2 hxX)
  have hWN : W ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (fun k hk => Subgroup.le_normalizer hk) (Subgroup.zpowers_le.2 hxN)
  have hKW : ∀ w ∈ W, ∀ k ∈ K, w * k * w⁻¹ ∈ K := fun w hw k hk =>
    (Subgroup.mem_normalizer_iff.1 (hWN hw) k).1 hk
  set O : Subgroup G := GLAPPrimeCoreOf p X with hO
  have hOn : ∀ w ∈ X, ∀ n ∈ O, w * n * w⁻¹ ∈ O := by
    intro w hw n hn
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hn
    refine Subgroup.mem_map.2 ⟨(⟨w, hw⟩ : ↥X) * z * (⟨w, hw⟩ : ↥X)⁻¹,
      (GLAPPrimeCore.normal p ↥X).conj_mem z hz ⟨w, hw⟩, ?_⟩
    simp
  set N : Subgroup G := K ⊓ O with hN
  have hNW : ∀ w ∈ W, ∀ n ∈ N, w * n * w⁻¹ ∈ N := by
    intro w hw n hn
    exact ⟨hKW w hw n hn.1, hOn w (hWX hw) n hn.2⟩
  have hNWle : N ≤ W := fun n hn => (le_sup_left : K ≤ W) hn.1
  have hNle : N ≤ K := inf_le_left
  have hNO : N ≤ O := inf_le_right
  let NW : Subgroup W := N.subgroupOf W
  have hNWn : NW.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ N := Subgroup.mem_subgroupOf.1 hn
    rw [Subgroup.mem_subgroupOf]
    have := hNW g.1 g.2 n hn'
    simpa using this
  have hcopNW : ¬ p ∣ Nat.card NW := by
    intro hdvd
    have h1 : Nat.card NW = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNWle).toEquiv
    rw [h1] at hdvd
    have h2 : Nat.card N ∣ Nat.card O := Subgroup.card_dvd_of_le hNO
    have hcop := i183_coprime_card_glaPPrimeCoreOf hp X
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop ((hdvd.trans h2))
  have hAp : IsPGroup p ((Subgroup.zpowers x).subgroupOf W) :=
    (isPGroup_of_isElemAbelian' hx).comap_of_injective W.subtype W.subtype_injective
  have hcent := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime p NW hcopNW
    ((Subgroup.zpowers x).subgroupOf W) hAp
  obtain ⟨⟨k, hkX⟩, hk, rfl⟩ := Subgroup.mem_map.1 hyK
  have hkK : k ∈ K := Subgroup.mem_subgroupOf.1 hk
  have hkW : k ∈ W := (le_sup_left : K ≤ W) hkK
  have hxW : x ∈ W := (le_sup_right : Subgroup.zpowers x ≤ W) (Subgroup.mem_zpowers x)
  have hcK : ⁅k, x⁆ ∈ K := by
    rw [commutatorElement_def]
    have h1 : x * k⁻¹ * x⁻¹ ∈ K := hKn _ (K.inv_mem hkK)
    have := K.mul_mem hkK h1
    simpa [mul_assoc] using this
  have hcX : ⁅k, x⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem (hKX hkK) hxX) (X.inv_mem (hKX hkK))) (X.inv_mem hxX)
  have hcO : ⁅k, x⁆ ∈ O := by
    refine idiag_mem_core_of_mk_eq_one hcX ?_
    have hc := commutatorElement_eq_one_iff_commute.2 hyE
    have e : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨⁅k, x⁆, hcX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) =
        ⁅QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨k, hKX hkK⟩,
          QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩⁆ := by
      rw [← map_commutatorElement]
      rfl
    rw [e]
    exact hc
  have hcN : ⁅k, x⁆ ∈ N := ⟨hcK, hcO⟩
  have hkx : Commute (QuotientGroup.mk' NW (⟨k, hkW⟩ : ↥W))
      (QuotientGroup.mk' NW (⟨x, hxW⟩ : ↥W)) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 hcN
  have hk_cent : (QuotientGroup.mk' NW (⟨k, hkW⟩ : ↥W)) ∈ Subgroup.centralizer
      (((Subgroup.zpowers x).subgroupOf W).map (QuotientGroup.mk' NW) : Set (↥W ⧸ NW)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hh
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hz)
    have hzeq : z = (⟨x, hxW⟩ : ↥W) ^ m := Subtype.ext (by simp [← hm])
    rw [hzeq, map_zpow]
    exact (hkx.symm.zpow_left m).eq
  rw [← hcent] at hk_cent
  obtain ⟨w, hw, hwk⟩ := Subgroup.mem_map.1 hk_cent
  have hwx : x * (w : G) = (w : G) * x := by
    have := Subgroup.mem_centralizer_iff.1 hw (⟨x, hxW⟩ : ↥W)
      (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers x))
    exact congrArg Subtype.val this
  have hwK : (w : G) ∈ K := by
    have h1 : w⁻¹ * (⟨k, hkW⟩ : ↥W) ∈ NW := QuotientGroup.eq.1 hwk
    have h2 : ((w⁻¹ * ⟨k, hkW⟩ : ↥W) : G) ∈ N := Subgroup.mem_subgroupOf.1 h1
    have h3 : (w : G)⁻¹ * k ∈ K := by simpa using h2.1
    rw [show (w : G) = k * ((w : G)⁻¹ * k)⁻¹ by group]
    exact K.mul_mem hkK (K.inv_mem h3)
  have hwX : (w : G) ∈ X := hWX w.2
  have hwO : (w : G)⁻¹ * k ∈ O := by
    have h1 : w⁻¹ * (⟨k, hkW⟩ : ↥W) ∈ NW := QuotientGroup.eq.1 hwk
    have h2 : ((w⁻¹ * ⟨k, hkW⟩ : ↥W) : G) ∈ N := Subgroup.mem_subgroupOf.1 h1
    simpa using h2.2
  have hyw : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨k, hkX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(w : G), hwX⟩ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 (O.inv_mem hwO)
    have hz' : (z : G) = ((w : G)⁻¹ * k)⁻¹ := hzeq
    have hzeq' : z = (⟨k, hkX⟩ : ↥X)⁻¹ * ⟨(w : G), hwX⟩ :=
      Subtype.ext (show (z : G) = k⁻¹ * (w : G) by rw [hz']; group)
    rw [hzeq'] at hz
    exact hz
  have hwC : (w : G) ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hwx
  exact Subgroup.mem_map.2 ⟨⟨(w : G), hwX⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hwK, hwC⟩),
    hyw.symm⟩

end Coprime

section Family

variable {G : Type} [Group G] [Finite G]

def i2Fam (M : Subgroup G) (x : G) : Set (Subgroup G) :=
  {M, GLBConj x M, GLBConj x (GLBConj x M)}

theorem i2Fam_conj_mem {M : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (n : ℕ) :
    GLBConj (x ^ n) M ∈ i2Fam M x := by
  have hn : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
  have hxn : x ^ n = x ^ (n % 3) := by
    conv_lhs => rw [hn, pow_add, pow_mul, hx3, one_pow, one_mul]
  rw [hxn]
  have hr : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize n % 3 = r at hr ⊢
  interval_cases r
  · left
    simp [gLBConj_one]
  · right; left
    simp
  · right; right
    simp [gLBConj_gLBConj, pow_two]

theorem i2Fam_exists {M : Subgroup G} {x : G} {C : Subgroup G} (hC : C ∈ i2Fam M x) :
    ∃ n : ℕ, n < 3 ∧ C = GLBConj (x ^ n) M := by
  simp only [i2Fam, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with h | h | h
  · exact ⟨0, by norm_num, by simp [h, gLBConj_one]⟩
  · exact ⟨1, by norm_num, by simp [h]⟩
  · exact ⟨2, by norm_num, by simp [h, gLBConj_gLBConj, pow_two]⟩

theorem i2Fam_comp {p : ℕ} {X M : Subgroup G} {x : G} (hM : GLAPComponent p X M) (hxX : x ∈ X) :
    ∀ C ∈ i2Fam M x, GLAPComponent p X C := by
  intro C hC
  obtain ⟨n, -, rfl⟩ := i2Fam_exists hC
  have hn : x ^ n ∈ X := X.pow_mem hxX n
  have := glaPComponent_gLBConj hM (x ^ n)
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)] at this

theorem i2Fam_inv {M : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) {e : G} (he : e ∈ Subgroup.zpowers x)
    {C : Subgroup G} (hC : C ∈ i2Fam M x) : GLBConj e C ∈ i2Fam M x := by
  obtain ⟨n, -, rfl⟩ := i2Fam_exists hC
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  obtain ⟨m, hm⟩ := idiag_zpow_nat (by norm_num : 0 < 3) (hx3 : x ^ 3 = 1) k
  rw [hm, gLBConj_gLBConj, ← pow_add]
  exact i2Fam_conj_mem hx3 _

theorem i2Fam_trans {M : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) {C C' : Subgroup G}
    (hC : C ∈ i2Fam M x) (hC' : C' ∈ i2Fam M x) :
    ∃ e ∈ Subgroup.zpowers x, GLBConj e C = C' := by
  obtain ⟨n, hn3, rfl⟩ := i2Fam_exists hC
  obtain ⟨n', -, rfl⟩ := i2Fam_exists hC'
  refine ⟨x ^ (n' + 3 - n), Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _, ?_⟩
  rw [gLBConj_gLBConj, ← pow_add]
  have e : n + (n' + 3 - n) = n' + 3 := by omega
  rw [e, pow_add, hx3, mul_one]

theorem i2Fam_ne {M : Subgroup G} {x : G} (h1 : GLBConj x M ≠ M)
    (h2 : GLBConj x (GLBConj x M) ≠ M) :
    ∀ C ∈ i2Fam M x, ∃ C₂ ∈ i2Fam M x, C₂ ≠ C := by
  intro C hC
  simp only [i2Fam, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with h | h | h
  · exact ⟨GLBConj x M, by simp [i2Fam], fun e => h1 (e.trans h)⟩
  · exact ⟨M, by simp [i2Fam], fun e => h1 (h.symm.trans e.symm)⟩
  · exact ⟨M, by simp [i2Fam], fun e => h2 (h.symm.trans e.symm)⟩

theorem i2Fam_sup (M : Subgroup G) (x : G) :
    (⨆ C : i2Fam M x, (C : Subgroup G)) = M ⊔ GLBConj x M ⊔ GLBConj x (GLBConj x M) := by
  apply le_antisymm
  · refine iSup_le fun C => ?_
    rcases C.2 with h | h | h
    · rw [h]
      exact le_sup_of_le_left (le_sup_left)
    · rw [h]
      exact le_sup_of_le_left (le_sup_right)
    · rw [h]
      exact le_sup_right
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact le_iSup (fun C : i2Fam M x => (C : Subgroup G)) ⟨M, Or.inl rfl⟩
    · exact le_iSup (fun C : i2Fam M x => (C : Subgroup G)) ⟨GLBConj x M, Or.inr (Or.inl rfl)⟩
    · exact le_iSup (fun C : i2Fam M x => (C : Subgroup G))
        ⟨GLBConj x (GLBConj x M), Or.inr (Or.inr rfl)⟩

end Family

section CentMod

variable {G : Type} [Group G] [Finite G]

theorem i2_centMod_central {p : ℕ} (hp : p.Prime) {X C : Subgroup G} (hC : GLAPComponent p X C)
    {n : G} (hnX : n ∈ X) (hn : n ∈ centModSubgroup p C) :
    ∀ c ∈ barX p X C, Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨n, hnX⟩) c := by
  intro c hc
  obtain ⟨⟨l, hlX⟩, hl, rfl⟩ := Subgroup.mem_map.1 hc
  have hlC : l ∈ C := Subgroup.mem_subgroupOf.1 hl
  have hO : ⁅l, n⁆ ∈ GLAPPrimeCoreOf p C := (mem_centModSubgroup.1 hn).2 l hlC
  obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 hO
  have hzker : z ∈ (barMap p hC.1).ker := by
    rw [ker_barMap_eq hp hC.1 hC.2.1]
    exact hz
  have hzX : (z : G) ∈ X := hC.1 z.2
  have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(z : G), hzX⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) = 1 := by
    have h0 := MonoidHom.mem_ker.1 hzker
    have h3 : ((barMap p hC.1 z : ↥(barX p X C)) : ↥X ⧸ GLAPPrimeCore p ↥X) =
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(z : G), hzX⟩ := rfl
    rw [← h3, h0]
    simp
  have hz_eq : (z : G) = ⁅l, n⁆ := hzeq
  have hcx : ⁅l, n⁆ ∈ X := by
    rw [← hz_eq]
    exact hzX
  have h2 : (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨⁅l, n⁆, hcx⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(z : G), hzX⟩ := by
    congr 1
    exact Subtype.ext hz_eq.symm
  have hcomm : Commute (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨l, hlX⟩)
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨n, hnX⟩) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    rw [show (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⁅(⟨l, hlX⟩ : ↥X), (⟨n, hnX⟩ : ↥X)⁆ : _) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨⁅l, n⁆, hcx⟩ from rfl, h2, h1]
  exact hcomm.symm

end CentMod

section KbStructure

variable {Y' : Type} [Group Y']

theorem i2_le_normalizer_of_comm {A B : Subgroup Y'} (h : ∀ a ∈ A, ∀ b ∈ B, Commute a b) :
    B ≤ Subgroup.normalizer (A : Set Y') := by
  intro b hb
  rw [mem_normalizer_iff_gLBConj_eq]
  exact idiag_gLBConj_eq_of_comm (fun y hy => (h y hy b hb).eq.symm)

theorem i2_kb_le_normalizer {D₀ D₁ D₂ : Subgroup Y'} (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b)
    (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c) :
    D₀ ⊔ D₁ ⊔ D₂ ≤ Subgroup.normalizer (D₀ : Set Y') := by
  refine sup_le (sup_le Subgroup.le_normalizer (i2_le_normalizer_of_comm h01)) ?_
  exact i2_le_normalizer_of_comm h02

theorem i2_dec_zero {D₀ D₁ D₂ : Subgroup Y'} (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b)
    (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c) (h12 : ∀ b ∈ D₁, ∀ c ∈ D₂, Commute b c)
    {y : Y'} (hy : y ∈ D₀ ⊔ D₁ ⊔ D₂) :
    ∃ a ∈ D₀, ∃ n ∈ Subgroup.centralizer (D₀ : Set Y'), y = a * n := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := i2_triple h01 h02 h12 hy
  refine ⟨a, ha, b * c, ?_, (mul_assoc a b c)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have e1 := (h01 d hd b hb).eq
  have e2 := (h02 d hd c hc).eq
  calc d * (b * c) = (d * b) * c := by group
    _ = (b * d) * c := by rw [e1]
    _ = b * (d * c) := by group
    _ = b * (c * d) := by rw [e2]
    _ = (b * c) * d := by group

theorem i2_dec_one {D₀ D₁ D₂ : Subgroup Y'} (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b)
    (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c) (h12 : ∀ b ∈ D₁, ∀ c ∈ D₂, Commute b c)
    {y : Y'} (hy : y ∈ D₀ ⊔ D₁ ⊔ D₂) :
    ∃ b ∈ D₁, ∃ n ∈ Subgroup.centralizer (D₁ : Set Y'), y = b * n := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := i2_triple h01 h02 h12 hy
  refine ⟨b, hb, a * c, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have e1 := (h01 a ha d hd).eq
    have e2 := (h12 d hd c hc).eq
    calc d * (a * c) = (d * a) * c := by group
      _ = (a * d) * c := by rw [← e1]
      _ = a * (d * c) := by group
      _ = a * (c * d) := by rw [e2]
      _ = (a * c) * d := by group
  · calc a * b * c = b * (a * c) := by
          rw [← mul_assoc, (h01 a ha b hb).eq, mul_assoc]
      _ = b * (a * c) := rfl

theorem i2_dec_two {D₀ D₁ D₂ : Subgroup Y'} (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b)
    (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c) (h12 : ∀ b ∈ D₁, ∀ c ∈ D₂, Commute b c)
    {y : Y'} (hy : y ∈ D₀ ⊔ D₁ ⊔ D₂) :
    ∃ c ∈ D₂, ∃ n ∈ Subgroup.centralizer (D₂ : Set Y'), y = c * n := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := i2_triple h01 h02 h12 hy
  refine ⟨c, hc, a * b, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have e1 := (h02 a ha d hd).eq
    have e2 := (h12 b hb d hd).eq
    calc d * (a * b) = (d * a) * b := by group
      _ = (a * d) * b := by rw [← e1]
      _ = a * (d * b) := by group
      _ = a * (b * d) := by rw [e2]
      _ = (a * b) * d := by group
  · calc a * b * c = a * (b * c) := by group
      _ = a * (c * b) := by rw [(h12 b hb c hc).eq]
      _ = (a * c) * b := by group
      _ = (c * a) * b := by rw [(h02 a ha c hc).eq]
      _ = c * (a * b) := by group

theorem i2_central_of_factors {D₀ D₁ D₂ : Subgroup Y'} (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b)
    (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c) (h12 : ∀ b ∈ D₁, ∀ c ∈ D₂, Commute b c)
    {y : Y'} (hyc0 : ∀ d ∈ D₀, d * y = y * d) (hyc1 : ∀ d ∈ D₁, d * y = y * d)
    (hyc2 : ∀ d ∈ D₂, d * y = y * d) {z : Y'} (hz : z ∈ D₀ ⊔ D₁ ⊔ D₂) : z * y = y * z := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := i2_triple h01 h02 h12 hz
  have ea := hyc0 a ha
  have eb := hyc1 b hb
  have ec := hyc2 c hc
  calc a * b * c * y = a * b * (c * y) := by group
    _ = a * b * (y * c) := by rw [ec]
    _ = a * (b * y) * c := by group
    _ = a * (y * b) * c := by rw [eb]
    _ = (a * y) * b * c := by group
    _ = (y * a) * b * c := by rw [ea]
    _ = y * (a * b * c) := by group

end KbStructure

section Centreless

theorem i2_center_quot_bot {G : Type} [Group G] (hG : CFSG.Open.IsQuasisimple G) :
    Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := by
  obtain ⟨hcomm, hsimple⟩ := hG
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (G ⧸ Subgroup.center G)) with h | h
  · exact h
  · exfalso
    have hall : ∀ q : G ⧸ Subgroup.center G, q ∈ Subgroup.center (G ⧸ Subgroup.center G) := by
      intro q
      rw [h]
      exact Subgroup.mem_top q
    have hk : (⊤ : Subgroup G) ≤ (QuotientGroup.mk' (Subgroup.center G)).ker := by
      rw [← hcomm]
      show ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ _
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact (Subgroup.mem_center_iff.1 (hall _) _).symm
    have hone : ∀ g : G, (QuotientGroup.mk' (Subgroup.center G) g : G ⧸ Subgroup.center G) = 1 :=
      fun g => MonoidHom.mem_ker.1 (hk (Subgroup.mem_top g))
    obtain ⟨a, b, hab⟩ := exists_pair_ne (G ⧸ Subgroup.center G)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) a
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) b
    exact hab ((hone g).trans (hone g').symm)

theorem i2_quot_centre_equiv {K' Q : Type} [Group K'] [Group Q] (O : Subgroup K') [O.Normal]
    (Λ : K' →* Q) (hsurj : Function.Surjective Λ)
    (hcentless : ∀ z : Q, (∀ q : Q, q * z = z * q) → z = 1)
    (hO : O ≤ Λ.ker) (hker : ∀ k : K', Λ k = 1 → ∀ k' : K', ⁅k, k'⁆ ∈ O) :
    ∃ e : (K' ⧸ O) ⧸ Subgroup.center (K' ⧸ O) ≃* Q,
      ∀ k : K', e (QuotientGroup.mk (QuotientGroup.mk k : K' ⧸ O)) = Λ k := by
  classical
  let Λ' : K' ⧸ O →* Q := QuotientGroup.lift O Λ hO
  have hΛ'surj : Function.Surjective Λ' := by
    intro q
    obtain ⟨k, rfl⟩ := hsurj q
    exact ⟨(k : K' ⧸ O), rfl⟩
  have hZ : Subgroup.center (K' ⧸ O) ≤ Λ'.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply hcentless
    intro q
    obtain ⟨w, rfl⟩ := hΛ'surj q
    have h1 := Subgroup.mem_center_iff.1 hz w
    have h2 := congrArg Λ' h1
    rw [map_mul, map_mul] at h2
    exact h2
  let Λ'' : (K' ⧸ O) ⧸ Subgroup.center (K' ⧸ O) →* Q := QuotientGroup.lift _ Λ' hZ
  have hcenter_of : ∀ x : K' ⧸ O, Λ' x = 1 → x ∈ Subgroup.center (K' ⧸ O) := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective O x
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective O y
    have hk : Λ k = 1 := hx
    have h1 : ⁅k', k⁆ ∈ O := by
      have h0 := hker k hk k'
      have e : ⁅k', k⁆ = ⁅k, k'⁆⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [e]
      exact O.inv_mem h0
    have hcm : Commute ((QuotientGroup.mk' O) k') ((QuotientGroup.mk' O) k) := by
      rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h1
    exact hcm.eq
  refine ⟨MulEquiv.ofBijective Λ'' ⟨?_, ?_⟩, fun k => rfl⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (K' ⧸ O)) x
    have : Λ' y = 1 := hx
    exact (QuotientGroup.eq_one_iff _).2 (hcenter_of y this)
  · intro q
    obtain ⟨x, hx⟩ := hΛ'surj q
    exact ⟨(QuotientGroup.mk' _ x : (K' ⧸ O) ⧸ Subgroup.center (K' ⧸ O)), hx⟩

end Centreless

section FamilyBar

variable {G : Type} [Group G] [Finite G]

theorem i2_K_normalized {M : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) :
    (∀ k ∈ ⨆ C : i2Fam M x, (C : Subgroup G), x * k * x⁻¹ ∈ ⨆ C : i2Fam M x, (C : Subgroup G)) ∧
    (∀ k ∈ ⨆ C : i2Fam M x, (C : Subgroup G), x⁻¹ * k * x ∈ ⨆ C : i2Fam M x, (C : Subgroup G)) := by
  constructor
  · intro k hk
    refine Subgroup.iSup_induction (fun C : i2Fam M x => (C : Subgroup G))
      (C := fun k => x * k * x⁻¹ ∈ ⨆ C : i2Fam M x, (C : Subgroup G)) hk ?_ ?_ ?_
    · intro C k hk'
      have hmem : GLBConj x⁻¹ (C : Subgroup G) ∈ i2Fam M x :=
        i2Fam_inv hx3 (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) C.2
      have hc : x * k * x⁻¹ ∈ GLBConj x⁻¹ (C : Subgroup G) := by
        rw [mem_gLBConj]
        simpa [mul_assoc] using hk'
      exact (le_iSup (fun C' : i2Fam M x => (C' : Subgroup G)) ⟨_, hmem⟩) hc
    · simp
    · intro a b ha hb
      have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
  · intro k hk
    refine Subgroup.iSup_induction (fun C : i2Fam M x => (C : Subgroup G))
      (C := fun k => x⁻¹ * k * x ∈ ⨆ C : i2Fam M x, (C : Subgroup G)) hk ?_ ?_ ?_
    · intro C k hk'
      have hmem : GLBConj x (C : Subgroup G) ∈ i2Fam M x :=
        i2Fam_inv hx3 (Subgroup.mem_zpowers x) C.2
      have hc : x⁻¹ * k * x ∈ GLBConj x (C : Subgroup G) := by
        rw [mem_gLBConj]
        simpa [mul_assoc] using hk'
      exact (le_iSup (fun C' : i2Fam M x => (C' : Subgroup G)) ⟨_, hmem⟩) hc
    · simp
    · intro a b ha hb
      have : x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb

theorem i2_barX_K_eq {p : ℕ} {X M : Subgroup G} {x : G} (hfam : ∀ C ∈ i2Fam M x, GLAPComponent p X C)
    (hKX : (⨆ C : i2Fam M x, (C : Subgroup G)) ≤ X) :
    barX p X (⨆ C : i2Fam M x, (C : Subgroup G)) = ⨆ C : i2Fam M x, barX p X (C : Subgroup G) := by
  apply le_antisymm
  · exact idiag_barX_le_kb (fun C hC => hfam C hC) le_rfl
  · refine iSup_le fun C => barX_mono p ?_
    exact le_iSup (fun C' : i2Fam M x => (C' : Subgroup G)) C

end FamilyBar

section JAnalysis

variable {G : Type} [Group G] [Finite G]

theorem i2_J_part {X K M J : Subgroup G} {x : G}
    (hM : GLAPComponent 3 X M) (hxX : x ∈ X) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (h1 : GLBConj x M ≠ M) (h2 : GLBConj x (GLBConj x M) ≠ M)
    (hKeq : K = M ⊔ GLBConj x M ⊔ GLBConj x (GLBConj x M))
    (hJK : J ≤ K) (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    barX 3 X J = GLALayer (barX 3 X K ⊓
        Subgroup.centralizer (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) ∧
      CFSG.Open.IsQuasisimple ↥(GLALayer (barX 3 X K ⊓
        Subgroup.centralizer (barX 3 X (Subgroup.zpowers x) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ∧
      (∀ C ∈ i2Fam M x, ∀ m ∈ C, ∃ j ∈ J, ∃ n ∈ centModSubgroup 3 C, m = j * n) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  set fam := i2Fam M x with hfam
  have hcomp : ∀ C ∈ fam, GLAPComponent 3 X C := i2Fam_comp hM hxX
  have hinv : ∀ C ∈ fam, ∀ e ∈ Subgroup.zpowers x, GLBConj e C ∈ fam :=
    fun C hC e he => i2Fam_inv hx3 he hC
  have htrans : ∀ C ∈ fam, ∀ C' ∈ fam, ∃ e ∈ Subgroup.zpowers x, GLBConj e C = C' :=
    fun C hC C' hC' => i2Fam_trans hx3 hC hC'
  have hne : ∀ C ∈ fam, ∃ C₂ ∈ fam, C₂ ≠ C := i2Fam_ne h1 h2
  have hM3 : M ∈ fam := by simp [fam, i2Fam]
  have hD : IsElemAbelian 3 (Subgroup.zpowers x) := idiag_elemAbelian_zpowers hx3
  have hdA : x ∉ (⊥ : Subgroup G) := fun h => hx1 (Subgroup.mem_bot.1 h)
  have hidx : (⊥ : Subgroup G).relIndex (Subgroup.zpowers x) = 3 := by
    rw [Subgroup.relIndex_bot_left, Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hAX : ∀ a ∈ (⊥ : Subgroup G), ∀ y ∈ X, a * y = y * a := by
    intro a ha y _
    rw [Subgroup.mem_bot.1 ha, one_mul, mul_one]
  have hKX : K ≤ X := by
    rw [hKeq]
    refine sup_le (sup_le ((hcomp M hM3).1) ((hcomp _ (by simp [fam, i2Fam])).1))
      ((hcomp _ (by simp [fam, i2Fam])).1)
  have hKsup : K = ⨆ C : fam, (C : Subgroup G) := by
    rw [hKeq]
    exact (i2Fam_sup M x).symm
  have hKb_eq : barX 3 X K = ⨆ C : fam, barX 3 X (C : Subgroup G) := by
    rw [hKsup]
    exact i2_barX_K_eq hcomp (by rw [← hKsup]; exact hKX)
  have hKn : ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro k hk
    rw [hKsup] at hk ⊢
    exact (i2_K_normalized hx3).1 k hk
  have hKn' : ∀ k ∈ K, x⁻¹ * k * x ∈ K := by
    intro k hk
    rw [hKsup] at hk ⊢
    exact (i2_K_normalized hx3).2 k hk
  set Ksup : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) := ⨆ C : fam, barX 3 X (C : Subgroup G) with hKs
  have hlay : GLALayer Ksup = Ksup := by
    refine le_antisymm (i25_layer_le _) ?_
    exact iSup_le fun C => i25_le_layer (idiag_barX_isComponent hcomp C.2)
  have hEnorm : barX 3 X (Subgroup.zpowers x) ≤ Subgroup.normalizer (Ksup : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    idiag_E_le_normalizer hinv (Subgroup.mem_zpowers x) (hxX)
  have hEab : IsElemAbelian 3 (barX 3 X (Subgroup.zpowers x)) := isElemAbelian_barX hD
  have htr : ∀ L L' : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), IsComponentOf L Ksup →
      IsComponentOf L' Ksup → ∃ e ∈ barX 3 X (Subgroup.zpowers x), GLBConj e L = L' :=
    fun L L' hL hL' => idiag_trans Nat.prime_three hD bot_le hidx (Subgroup.mem_zpowers x) hdA hxX
      hAX hcomp htrans hL hL'
  have hfree : ∀ e ∈ barX 3 X (Subgroup.zpowers x), e ≠ 1 →
      ∀ L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), IsComponentOf L Ksup → GLBConj e L ≠ L :=
    fun e he he1 L hL => idiag_free Nat.prime_three hD bot_le hidx (Subgroup.mem_zpowers x) hdA hxX
      hAX hcomp hne htrans he he1 hL
  have hI25 := input2_5_proved _ 3 Nat.prime_three Ksup (barX 3 X (Subgroup.zpowers x)) hlay hEnorm
    hEab htr hfree
  obtain ⟨hI25a, hI25b⟩ := hI25
  set E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) := barX 3 X (Subgroup.zpowers x) with hEdef
  set Dl : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
    GLALayer (Ksup ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) with hDldef
  set W : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X) :=
    (Subgroup.center ↥Ksup).map Ksup.subtype ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))
    with hWdef
  have hsplit : Ksup ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) = Dl ⊔ W := hI25b
  have hWK : W ≤ Ksup := inf_le_left.trans (Subgroup.map_subtype_le _)
  have hWc : ∀ w ∈ W, ∀ g ∈ Ksup, Commute w g := by
    intro w hw g hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw.1
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)).symm
  have hJX : J ≤ X := hJK.trans hKX
  have hJsup : J ≤ ⨆ C : fam, (C : Subgroup G) := hKsup ▸ hJK
  have hbarJK : barX 3 X J ≤ Ksup := idiag_barX_le_kb hcomp hJsup
  have hJD : J ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro j hj
    have hjx : j ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.1 (hJ.1 hj)).2
    have hc : Commute x j := Subgroup.mem_centralizer_iff.1 hjx x rfl
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hc.zpow_left k).eq
  have hbarJC : barX 3 X J ≤ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    idiag_barX_le_centralizer hJD (Subgroup.mem_zpowers x) le_rfl
  have hbarJKC : barX 3 X J ≤ Ksup ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
    le_inf hbarJK hbarJC
  have hJDl : barX 3 X J ≤ Dl :=
    idiag_barX_le_layer hJ hJX hsplit inf_le_left hWK hWc hbarJKC
  have hDle : Dl ≤ barX 3 X (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
    intro y hy
    have hyC : y ∈ Ksup ⊓ Subgroup.centralizer (E : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      rw [hsplit]
      exact (le_sup_left : Dl ≤ Dl ⊔ W) hy
    obtain ⟨hyK, hyE⟩ := hyC
    have hyK' : y ∈ barX 3 X K := by
      rw [hKb_eq]
      exact hyK
    have hcm : Commute y (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x, hxX⟩) := by
      have hmem : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨x, hxX⟩ : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈
          barX 3 X (Subgroup.zpowers x) :=
        Subgroup.mem_map.2 ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers x), rfl⟩
      exact (Subgroup.mem_centralizer_iff.1 hyE _ hmem).symm
    exact i2_coprime Nat.prime_three hKX hxX hD hKn hKn' hyK' hcm
  have hHX : K ⊓ Subgroup.centralizer ({x} : Set G) ≤ X := inf_le_left.trans hKX
  have hDq : CFSG.Open.IsQuasisimple ↥Dl := by
    obtain ⟨Z, hZn, hZc, ⟨φ⟩⟩ := hI25a _ (idiag_barX_isComponent hcomp hM3)
    exact Components.quasisimple_of_equiv φ
      (Quasisimple.central_quotient (idiag_barX_isComponent hcomp hM3).2.2 Z hZc)
  have hDJ : Dl ≤ barX 3 X J :=
    idiag_layer_le_barX Nat.prime_three hJ hJX hHX hDle hDq hJDl
  have hlift : ∀ C ∈ fam, ∀ m ∈ C, ∃ j ∈ J, ∃ n ∈ centModSubgroup 3 C, m = j * n := by
    intro C hC m hm
    exact idiag_lift Nat.prime_three hp2 bot_le hidx hD (Subgroup.mem_zpowers x) hxX hdA hAX hcomp hinv
      hne htrans hC hm rfl hsplit hWK hWc hDJ
  refine ⟨?_, ?_, hlift⟩
  · rw [hKb_eq]
    exact le_antisymm hJDl hDJ
  · rw [hKb_eq]
    exact hDq

end JAnalysis

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem i2_le_core {H : Type} [Group H] {p : ℕ} {S : Subgroup H} [S.Normal]
    (hc : Nat.Coprime p (Nat.card S)) : S ≤ GLAPPrimeCore p H := by
  show S ≤ CFSG.pPrimeCore p H
  exact le_sSup ⟨inferInstance, hc⟩

theorem i2_core_barX_eq_bot {X C : Subgroup G} (hC : GLAPComponent 3 X C) :
    GLAPPrimeCore 3 ↥(barX 3 X C) = ⊥ := by
  have e := quotEquivBarX Nat.prime_three hC.1 hC.2.1
  have h := glaPPrimeCore_map_iso 3 e
  rw [glaPPrimeCore_quotient_eq_bot Nat.prime_three, Subgroup.map_bot] at h
  exact h.symm

theorem i2_psimple_centreless {X M : Subgroup G} (hM : GLAPComponent 3 X M) :
    ∀ z : PSimple 3 M, (∀ q : PSimple 3 M, q * z = z * q) → z = 1 := by
  intro z hz
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 M) :=
    Components.quasisimple_of_equiv (quotEquivBarX Nat.prime_three hM.1 hM.2.1) hM.2.2.1.2.2
  have h := i2_center_quot_bot hq
  have hz' : z ∈ Subgroup.center (PSimple 3 M) := Subgroup.mem_center_iff.2 hz
  rw [h, Subgroup.mem_bot] at hz'
  exact hz'

theorem i2_psimple_nontrivial {X M : Subgroup G} (hM : GLAPComponent 3 X M) :
    Nontrivial (PSimple 3 M) := by
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 M) :=
    Components.quasisimple_of_equiv (quotEquivBarX Nat.prime_three hM.1 hM.2.1) hM.2.2.1.2.2
  obtain ⟨_, hsimple⟩ := hq
  exact IsSimpleGroup.toNontrivial

theorem i2_commute_of_bot {Y' : Type} [Group Y'] {A B : Subgroup Y'} (h : ⁅A, B⁆ = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
  intro a ha b hb
  rw [← commutatorElement_eq_one_iff_commute]
  have hm := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot] at hm
  exact hm

theorem i2_normal_factors {Y' : Type} [Group Y'] {D₀ D₁ D₂ : Subgroup Y'}
    (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b) (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c)
    (h12 : ∀ b ∈ D₁, ∀ c ∈ D₂, Commute b c) :
    (∀ g ∈ D₀ ⊔ D₁ ⊔ D₂, ∀ d ∈ D₀, g * d * g⁻¹ ∈ D₀) ∧
    (∀ g ∈ D₀ ⊔ D₁ ⊔ D₂, ∀ d ∈ D₁, g * d * g⁻¹ ∈ D₁) ∧
    (∀ g ∈ D₀ ⊔ D₁ ⊔ D₂, ∀ d ∈ D₂, g * d * g⁻¹ ∈ D₂) := by
  have h10 : ∀ a ∈ D₁, ∀ b ∈ D₀, Commute a b := fun a ha b hb => (h01 b hb a ha).symm
  have h20 : ∀ a ∈ D₂, ∀ b ∈ D₀, Commute a b := fun a ha b hb => (h02 b hb a ha).symm
  have h21 : ∀ a ∈ D₂, ∀ c ∈ D₁, Commute a c := fun a ha c hc => (h12 c hc a ha).symm
  have e1 : D₀ ⊔ D₁ ⊔ D₂ = D₁ ⊔ D₀ ⊔ D₂ := by rw [sup_comm D₀ D₁]
  have e2 : D₀ ⊔ D₁ ⊔ D₂ = D₂ ⊔ D₀ ⊔ D₁ := by rw [sup_comm (D₀ ⊔ D₁) D₂, sup_assoc]
  refine ⟨fun g hg d hd => ?_, fun g hg d hd => ?_, fun g hg d hd => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 (i2_kb_le_normalizer h01 h02 hg) d).1 hd
  · rw [e1] at hg
    exact (Subgroup.mem_normalizer_iff.1 (i2_kb_le_normalizer h10 h12 hg) d).1 hd
  · rw [e2] at hg
    exact (Subgroup.mem_normalizer_iff.1 (i2_kb_le_normalizer h20 h21 hg) d).1 hd

theorem i2_central_of_normal {Y' : Type} [Group Y'] {D₀ D₁ D₂ Kb N : Subgroup Y'}
    (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b) (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c)
    (h12 : ∀ b ∈ D₁, ∀ c ∈ D₂, Commute b c) (hKb : Kb = D₀ ⊔ D₁ ⊔ D₂)
    (hD₀ : ∀ g ∈ Kb, ∀ d ∈ D₀, g * d * g⁻¹ ∈ D₀) (hD₁ : ∀ g ∈ Kb, ∀ d ∈ D₁, g * d * g⁻¹ ∈ D₁)
    (hD₂ : ∀ g ∈ Kb, ∀ d ∈ D₂, g * d * g⁻¹ ∈ D₂)
    (hD₀K : D₀ ≤ Kb) (hD₁K : D₁ ≤ Kb) (hD₂K : D₂ ≤ Kb)
    (hN : ∀ g ∈ Kb, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hNK : N ≤ Kb)
    (hN₀ : N ⊓ D₀ = ⊥) (hN₁ : N ⊓ D₁ = ⊥) (hN₂ : N ⊓ D₂ = ⊥)
    {n : Y'} (hn : n ∈ N) : ∀ g ∈ Kb, g * n = n * g := by
  have hfac : ∀ (D : Subgroup Y'), D ≤ Kb → (∀ g ∈ Kb, ∀ d ∈ D, g * d * g⁻¹ ∈ D) →
      N ⊓ D = ⊥ → ∀ d ∈ D, d * n = n * d := by
    intro D hDK hD hND d hd
    have h1 : n * (d * n⁻¹ * d⁻¹) ∈ N := N.mul_mem hn (hN d (hDK hd) n⁻¹ (N.inv_mem hn))
    have h2 : n * (d * n⁻¹ * d⁻¹) ∈ D := by
      have h3 : n * d * n⁻¹ ∈ D := hD n (hNK hn) d hd
      have h4 : n * d * n⁻¹ * d⁻¹ ∈ D := D.mul_mem h3 (D.inv_mem hd)
      have e : n * (d * n⁻¹ * d⁻¹) = n * d * n⁻¹ * d⁻¹ := by group
      rw [e]
      exact h4
    have hmem : n * (d * n⁻¹ * d⁻¹) ∈ N ⊓ D := ⟨h1, h2⟩
    rw [hND, Subgroup.mem_bot] at hmem
    have h5 : n * d * n⁻¹ = d := by
      have e : n * d * n⁻¹ * d⁻¹ = 1 := by
        have e' : n * d * n⁻¹ * d⁻¹ = n * (d * n⁻¹ * d⁻¹) := by group
        rw [e']
        exact hmem
      exact mul_inv_eq_one.1 e
    calc d * n = (n * d * n⁻¹) * n := by rw [h5]
      _ = n * d := by group
  intro g hg
  rw [hKb] at hg
  exact i2_central_of_factors h01 h02 h12 (hfac D₀ hD₀K hD₀ hN₀) (hfac D₁ hD₁K hD₁ hN₁)
    (hfac D₂ hD₂K hD₂ hN₂) hg

theorem i2_inf_bot {Y' : Type} [Group Y'] {Kb D N : Subgroup Y'} (hDK : D ≤ Kb)
    (hN : ∀ g ∈ Kb, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hcop : Nat.Coprime 3 (Nat.card N))
    (hcore : GLAPPrimeCore 3 ↥D = ⊥) : N ⊓ D = ⊥ := by
  have hdvd : Nat.card ↥((N ⊓ D).subgroupOf D) ∣ Nat.card N := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ D ≤ D)).toEquiv]
    exact Subgroup.card_dvd_of_le (inf_le_left : N ⊓ D ≤ N)
  have hc : Nat.Coprime 3 (Nat.card ↥((N ⊓ D).subgroupOf D)) :=
    Nat.Coprime.coprime_dvd_right hdvd hcop
  have hnorm : ((N ⊓ D).subgroupOf D).Normal := by
    refine ⟨fun s hs g => ?_⟩
    have hs' : (s : Y') ∈ N ⊓ D := Subgroup.mem_subgroupOf.1 hs
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.2 ⟨hN g (hDK g.2) s (Subgroup.mem_inf.1 hs').1, ?_⟩
    exact D.mul_mem (D.mul_mem g.2 (Subgroup.mem_inf.1 hs').2) (D.inv_mem g.2)
  haveI := hnorm
  have hle : (N ⊓ D).subgroupOf D ≤ GLAPPrimeCore 3 ↥D := i2_le_core hc
  rw [hcore] at hle
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_bot]
    have hmem : (⟨y, (Subgroup.mem_inf.1 hy).2⟩ : ↥D) ∈ (N ⊓ D).subgroupOf D :=
      Subgroup.mem_subgroupOf.2 hy
    exact congrArg Subtype.val (Subgroup.mem_bot.1 (hle hmem))
  · intro hy
    rw [Subgroup.mem_bot] at hy
    rw [hy]
    exact Subgroup.one_mem _

theorem i2_ker_barMap_le_core {X K : Subgroup G} (hKX : K ≤ X) :
    (barMap 3 hKX).ker ≤ GLAPPrimeCore 3 ↥K := by
  have hT : ((barMap 3 hKX).ker.map K.subtype) ≤ GLAPPrimeCoreOf 3 X := by
    rintro _ ⟨k, hk, rfl⟩
    have hk1 : barMap 3 hKX k = 1 := hk
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨(k : G), hKX k.2⟩ :
        ↥X ⧸ GLAPPrimeCore 3 ↥X) = 1 :=
      congrArg Subtype.val hk1
    exact idiag_mem_core_of_mk_eq_one (hKX k.2) h1
  have hcard : Nat.card ((barMap 3 hKX).ker.map K.subtype) = Nat.card (barMap 3 hKX).ker :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hc : Nat.Coprime 3 (Nat.card (barMap 3 hKX).ker) := by
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hT)
      (i183_coprime_card_glaPPrimeCoreOf Nat.prime_three X)
  exact i2_le_core hc

theorem i2_mu_exists {Y' Q : Type} [Group Y'] [Group Q] {D Kb : Subgroup Y'} (hDKb : D ≤ Kb)
    (hDn : ∀ y ∈ Kb, ∀ d ∈ D, y * d * y⁻¹ ∈ D)
    (hdec : ∀ y ∈ Kb, ∃ a ∈ D, ∃ n ∈ Subgroup.centralizer (D : Set Y'), y = a * n)
    (θ : (↥D ⧸ Subgroup.center ↥D) ≃* Q) :
    ∃ μ : ↥Kb →* Q, Function.Surjective μ ∧
      ∀ k : ↥Kb, μ k = 1 ↔ ∀ d ∈ D, d * (k : Y') = (k : Y') * d := by
  haveI := i2_centralizer_normal hDn
  obtain ⟨e⟩ := i2_centralizer_quot_iso hDKb hDn hdec
  refine ⟨θ.toMonoidHom.comp (e.toMonoidHom.comp
    (QuotientGroup.mk' (((Subgroup.centralizer (D : Set Y')) ⊓ Kb).subgroupOf Kb))), ?_, ?_⟩
  · exact θ.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  · intro k
    have hmem : k ∈ ((Subgroup.centralizer (D : Set Y')) ⊓ Kb).subgroupOf Kb ↔
        ∀ d ∈ D, d * (k : Y') = (k : Y') * d := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · rintro ⟨h, -⟩ d hd
        exact (Subgroup.mem_centralizer_iff.1 h) d hd
      · intro h
        exact ⟨Subgroup.mem_centralizer_iff.2 (fun d hd => h d hd), k.2⟩
    rw [← hmem]
    show θ (e (QuotientGroup.mk' _ k)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff θ, MulEquiv.map_eq_one_iff e, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]

theorem i2_factor_hit {Y' Q : Type} [Group Y'] [Group Q] {D Kb : Subgroup Y'} (hD : D ≤ Kb)
    (hdec : ∀ y ∈ Kb, ∃ a ∈ D, ∃ n ∈ Subgroup.centralizer (D : Set Y'), y = a * n)
    {μ : ↥Kb →* Q} (hsurj : Function.Surjective μ)
    (hker : ∀ k : ↥Kb, μ k = 1 ↔ ∀ d ∈ D, d * (k : Y') = (k : Y') * d) (q : Q) :
    ∃ a, ∃ ha : a ∈ D, μ ⟨a, hD ha⟩ = q := by
  obtain ⟨y, hy⟩ := hsurj q
  obtain ⟨a, ha, n, hn, hyan⟩ := hdec y.1 y.2
  have hnKb : n ∈ Kb := by
    have hn' : n = a⁻¹ * y.1 := by rw [hyan]; group
    rw [hn']
    exact Kb.mul_mem (Kb.inv_mem (hD ha)) y.2
  have hμn : μ ⟨n, hnKb⟩ = 1 :=
    (hker ⟨n, hnKb⟩).2 (fun d hd => Subgroup.mem_centralizer_iff.1 hn d hd)
  refine ⟨a, ha, ?_⟩
  have hsplit : y = ⟨a, hD ha⟩ * ⟨n, hnKb⟩ := Subtype.ext hyan
  rw [← hy, hsplit, map_mul, hμn, mul_one]

theorem i2_mu_central {Γ Q : Type} [Group Γ] [Group Q]
    (hcl : ∀ z : Q, (∀ q : Q, q * z = z * q) → z = 1)
    {μ : Γ →* Q} (hs : Function.Surjective μ) {z : Γ} (hz : ∀ g : Γ, g * z = z * g) :
    μ z = 1 := by
  apply hcl
  intro q
  obtain ⟨g, rfl⟩ := hs q
  have h := congrArg μ (hz g)
  rw [map_mul, map_mul] at h
  exact h

theorem i2_prod_central {Y' : Type} [Group Y'] {D₀ D₁ D₂ Kb : Subgroup Y'}
    (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b) (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c)
    (h12 : ∀ b ∈ D₁, ∀ c ∈ D₂, Commute b c) (hKb : Kb = D₀ ⊔ D₁ ⊔ D₂) {k : Y'}
    (h0 : ∀ d ∈ D₀, d * k = k * d) (h1 : ∀ d ∈ D₁, d * k = k * d)
    (h2 : ∀ d ∈ D₂, d * k = k * d) : ∀ g ∈ Kb, g * k = k * g := by
  intro g hg
  rw [hKb] at hg
  exact i2_central_of_factors h01 h02 h12 h0 h1 h2 hg

theorem i2_prod_surj {Y' Q : Type} [Group Y'] [Group Q] {D₀ D₁ D₂ Kb : Subgroup Y'}
    (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b) (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c)
    (h12 : ∀ b ∈ D₁, ∀ c ∈ D₂, Commute b c) (hKb : Kb = D₀ ⊔ D₁ ⊔ D₂)
    (hD₀K : D₀ ≤ Kb) (hD₁K : D₁ ≤ Kb) (hD₂K : D₂ ≤ Kb)
    {μ₀ μ₁ μ₂ : ↥Kb →* Q}
    (hk₀ : ∀ k : ↥Kb, μ₀ k = 1 ↔ ∀ d ∈ D₀, d * (k : Y') = (k : Y') * d)
    (hk₁ : ∀ k : ↥Kb, μ₁ k = 1 ↔ ∀ d ∈ D₁, d * (k : Y') = (k : Y') * d)
    (hk₂ : ∀ k : ↥Kb, μ₂ k = 1 ↔ ∀ d ∈ D₂, d * (k : Y') = (k : Y') * d)
    (hs₀ : Function.Surjective μ₀) (hs₁ : Function.Surjective μ₁)
    (hs₂ : Function.Surjective μ₂) :
    Function.Surjective (μ₀.prod (μ₁.prod μ₂)) := by
  have dec₀ : ∀ y ∈ Kb, ∃ a ∈ D₀, ∃ n ∈ Subgroup.centralizer (D₀ : Set Y'), y = a * n :=
    fun y hy => i2_dec_zero h01 h02 h12 (by rw [← hKb]; exact hy)
  have dec₁ : ∀ y ∈ Kb, ∃ a ∈ D₁, ∃ n ∈ Subgroup.centralizer (D₁ : Set Y'), y = a * n :=
    fun y hy => i2_dec_one h01 h02 h12 (by rw [← hKb]; exact hy)
  have dec₂ : ∀ y ∈ Kb, ∃ a ∈ D₂, ∃ n ∈ Subgroup.centralizer (D₂ : Set Y'), y = a * n :=
    fun y hy => i2_dec_two h01 h02 h12 (by rw [← hKb]; exact hy)
  intro y
  obtain ⟨q₀, q₁, q₂⟩ := y
  obtain ⟨a₀, ha₀, h₀⟩ := i2_factor_hit hD₀K dec₀ hs₀ hk₀ q₀
  obtain ⟨a₁, ha₁, h₁⟩ := i2_factor_hit hD₁K dec₁ hs₁ hk₁ q₁
  obtain ⟨a₂, ha₂, h₂⟩ := i2_factor_hit hD₂K dec₂ hs₂ hk₂ q₂
  have e01 : μ₁ ⟨a₀, hD₀K ha₀⟩ = 1 := (hk₁ _).2 (fun d hd => (h01 a₀ ha₀ d hd).eq.symm)
  have e02 : μ₂ ⟨a₀, hD₀K ha₀⟩ = 1 := (hk₂ _).2 (fun d hd => (h02 a₀ ha₀ d hd).eq.symm)
  have e10 : μ₀ ⟨a₁, hD₁K ha₁⟩ = 1 := (hk₀ _).2 (fun d hd => (h01 d hd a₁ ha₁).eq)
  have e12 : μ₂ ⟨a₁, hD₁K ha₁⟩ = 1 := (hk₂ _).2 (fun d hd => (h12 a₁ ha₁ d hd).eq.symm)
  have e20 : μ₀ ⟨a₂, hD₂K ha₂⟩ = 1 := (hk₀ _).2 (fun d hd => (h02 d hd a₂ ha₂).eq)
  have e21 : μ₁ ⟨a₂, hD₂K ha₂⟩ = 1 := (hk₁ _).2 (fun d hd => (h12 d hd a₂ ha₂).eq)
  obtain ⟨k, hk⟩ : ∃ k : ↥Kb, k = ⟨a₀, hD₀K ha₀⟩ * ⟨a₁, hD₁K ha₁⟩ * ⟨a₂, hD₂K ha₂⟩ :=
    ⟨_, rfl⟩
  refine ⟨k, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · show μ₀ k = q₀
    rw [hk, map_mul, map_mul, e10, e20, h₀, mul_one, mul_one]
  · show μ₁ k = q₁
    rw [hk, map_mul, map_mul, e01, e21, h₁, one_mul, mul_one]
  · show μ₂ k = q₂
    rw [hk, map_mul, map_mul, e02, e12, h₂, one_mul, one_mul]

theorem i2_Kb_stage {Y' Q : Type} [Group Y'] [Group Q] {D₀ D₁ D₂ Kb : Subgroup Y'}
    (h01 : ∀ a ∈ D₀, ∀ b ∈ D₁, Commute a b) (h02 : ∀ a ∈ D₀, ∀ c ∈ D₂, Commute a c)
    (h12 : ∀ b ∈ D₁, ∀ c ∈ D₂, Commute b c) (hKb : Kb = D₀ ⊔ D₁ ⊔ D₂)
    (hD₀K : D₀ ≤ Kb) (hD₁K : D₁ ≤ Kb) (hD₂K : D₂ ≤ Kb)
    (θ₀ : (↥D₀ ⧸ Subgroup.center ↥D₀) ≃* Q) (θ₁ : (↥D₁ ⧸ Subgroup.center ↥D₁) ≃* Q)
    (θ₂ : (↥D₂ ⧸ Subgroup.center ↥D₂) ≃* Q)
    (hcl : ∀ z : Q, (∀ q : Q, q * z = z * q) → z = 1) :
    ∃ μ₀ μ₁ μ₂ : ↥Kb →* Q,
      (∀ k : ↥Kb, μ₀ k = 1 ↔ ∀ d ∈ D₀, d * (k : Y') = (k : Y') * d) ∧
      (∀ k : ↥Kb, μ₁ k = 1 ↔ ∀ d ∈ D₁, d * (k : Y') = (k : Y') * d) ∧
      (∀ k : ↥Kb, μ₂ k = 1 ↔ ∀ d ∈ D₂, d * (k : Y') = (k : Y') * d) ∧
      Function.Surjective μ₀ ∧ Function.Surjective μ₁ ∧ Function.Surjective μ₂ ∧
      Function.Surjective (μ₀.prod (μ₁.prod μ₂)) ∧
      (∀ k : ↥Kb, μ₀ k = 1 → μ₁ k = 1 → μ₂ k = 1 → ∀ g ∈ Kb, g * (k : Y') = (k : Y') * g) ∧
      (∀ z : ↥Kb, (∀ g : ↥Kb, g * z = z * g) → μ₀ z = 1 ∧ μ₁ z = 1 ∧ μ₂ z = 1) := by
  have dec₀ : ∀ y ∈ Kb, ∃ a ∈ D₀, ∃ n ∈ Subgroup.centralizer (D₀ : Set Y'), y = a * n :=
    fun y hy => i2_dec_zero h01 h02 h12 (by rw [← hKb]; exact hy)
  have dec₁ : ∀ y ∈ Kb, ∃ a ∈ D₁, ∃ n ∈ Subgroup.centralizer (D₁ : Set Y'), y = a * n :=
    fun y hy => i2_dec_one h01 h02 h12 (by rw [← hKb]; exact hy)
  have dec₂ : ∀ y ∈ Kb, ∃ a ∈ D₂, ∃ n ∈ Subgroup.centralizer (D₂ : Set Y'), y = a * n :=
    fun y hy => i2_dec_two h01 h02 h12 (by rw [← hKb]; exact hy)
  obtain ⟨n0, n1, n2⟩ := i2_normal_factors h01 h02 h12
  obtain ⟨μ₀, hs₀, hk₀⟩ := i2_mu_exists hD₀K
    (fun g hg d hd => n0 g (by rw [← hKb]; exact hg) d hd) dec₀ θ₀
  obtain ⟨μ₁, hs₁, hk₁⟩ := i2_mu_exists hD₁K
    (fun g hg d hd => n1 g (by rw [← hKb]; exact hg) d hd) dec₁ θ₁
  obtain ⟨μ₂, hs₂, hk₂⟩ := i2_mu_exists hD₂K
    (fun g hg d hd => n2 g (by rw [← hKb]; exact hg) d hd) dec₂ θ₂
  refine ⟨μ₀, μ₁, μ₂, hk₀, hk₁, hk₂, hs₀, hs₁, hs₂,
    i2_prod_surj h01 h02 h12 hKb hD₀K hD₁K hD₂K hk₀ hk₁ hk₂ hs₀ hs₁ hs₂, ?_, ?_⟩
  · intro k h0 h1 h2 g hg
    exact i2_prod_central h01 h02 h12 hKb ((hk₀ k).1 h0) ((hk₁ k).1 h1) ((hk₂ k).1 h2) g hg
  · intro z hz
    exact ⟨i2_mu_central hcl hs₀ hz, i2_mu_central hcl hs₁ hz, i2_mu_central hcl hs₂ hz⟩

theorem i2_prod3_centreless {Q : Type} [Group Q]
    (hcl : ∀ z : Q, (∀ q : Q, q * z = z * q) → z = 1) :
    ∀ z : Q × Q × Q, (∀ q : Q × Q × Q, q * z = z * q) → z = 1 := by
  rintro ⟨z0, z1, z2⟩ hz
  have h0 : z0 = 1 := hcl z0 (fun q => by
    have := congrArg Prod.fst (hz (q, 1, 1))
    simpa using this)
  have h1 : z1 = 1 := hcl z1 (fun q => by
    have := congrArg (fun p : Q × Q × Q => p.2.1) (hz (1, q, 1))
    simpa using this)
  have h2 : z2 = 1 := hcl z2 (fun q => by
    have := congrArg (fun p : Q × Q × Q => p.2.2) (hz (1, 1, q))
    simpa using this)
  subst h0 h1 h2
  rfl

theorem i2_K_abstract {Kg Kb Q : Type} [Group Kg] [Group Kb] [Group Q] (N : Subgroup Kg)
    [N.Normal] (ε : Kg →* Kb) (hεs : Function.Surjective ε) (hεk : ε.ker ≤ N)
    {Λ : Kb →* Q} (hΛs : Function.Surjective Λ)
    (hcl : ∀ z : Q, (∀ q : Q, q * z = z * q) → z = 1)
    (hcen_of : ∀ k : Kb, Λ k = 1 → ∀ g : Kb, g * k = k * g)
    (hcen_to : ∀ z : Kb, (∀ g : Kb, g * z = z * g) → Λ z = 1)
    (hNc : ∀ n ∈ N, ∀ g : Kb, g * ε n = ε n * g) :
    ∃ e : (Kg ⧸ N) ⧸ Subgroup.center (Kg ⧸ N) ≃* Q,
      ∀ k : Kg, e (QuotientGroup.mk (QuotientGroup.mk k : Kg ⧸ N)) = Λ (ε k) := by
  have hO : N ≤ (Λ.comp ε).ker := by
    intro n hn
    exact MonoidHom.mem_ker.2 (hcen_to (ε n) (hNc n hn))
  have hker : ∀ k : Kg, (Λ.comp ε) k = 1 → ∀ k' : Kg, ⁅k, k'⁆ ∈ N := by
    intro k hk k'
    have hc : ∀ g : Kb, g * ε k = ε k * g := hcen_of (ε k) hk
    refine hεk ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (hc (ε k')).symm
  obtain ⟨e, he⟩ := i2_quot_centre_equiv N (Λ.comp ε) (hΛs.comp hεs) hcl hO hker
  exact ⟨e, fun k => he k⟩

theorem i2_J_abstract {Jg DJ Q : Type} [Group Jg] [Group DJ] [Group Q] (N : Subgroup Jg)
    [N.Normal] (ε : Jg →* DJ) (hεs : Function.Surjective ε) (hεk : ε.ker ≤ N)
    (hDq : CFSG.Open.IsQuasisimple DJ) (hNtop : N ≠ ⊤)
    (ψ : DJ →* Q) (hψs : Function.Surjective ψ)
    (hcl : ∀ z : Q, (∀ q : Q, q * z = z * q) → z = 1) (hQnt : Nontrivial Q) :
    (∀ n ∈ N, ψ (ε n) = 1) ∧ (∀ j : Jg, ψ (ε j) = 1 → ∀ j' : Jg, ⁅j, j'⁆ ∈ N) := by
  haveI hNmap : (N.map ε).Normal := Subgroup.Normal.map inferInstance ε hεs
  have hÑ : N.map ε ≠ ⊤ := by
    intro htop
    apply hNtop
    rw [eq_top_iff]
    intro j _
    have hj : ε j ∈ N.map ε := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnj⟩ := Subgroup.mem_map.1 hj
    have hk : n⁻¹ * j ∈ ε.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnj, inv_mul_cancel]
    have hm := N.mul_mem hn (hεk hk)
    simpa using hm
  rcases Quasisimple.normal_le_center_or_eq_top hDq (N.map ε) with hle | htop
  swap
  · exact absurd htop hÑ
  have hcen : ∀ n ∈ N, ∀ g : DJ, g * ε n = ε n * g := fun n hn g =>
    Subgroup.mem_center_iff.1 (hle (Subgroup.mem_map.2 ⟨n, hn, rfl⟩)) g
  have hpart1 : ∀ n ∈ N, ψ (ε n) = 1 := fun n hn => i2_mu_central hcl hψs (hcen n hn)
  refine ⟨hpart1, fun j hj j' => ?_⟩
  rcases Quasisimple.normal_le_center_or_eq_top hDq ψ.ker with hS | hS
  · have hcj : ε j ∈ Subgroup.center DJ := hS (MonoidHom.mem_ker.2 hj)
    refine hεk ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.1 hcj (ε j')).symm
  · exfalso
    obtain ⟨u, v, huv⟩ := exists_pair_ne Q
    obtain ⟨y1, rfl⟩ := hψs u
    obtain ⟨y2, rfl⟩ := hψs v
    have h1 : ψ y1 = 1 := MonoidHom.mem_ker.1 (by rw [hS]; exact Subgroup.mem_top _)
    have h2 : ψ y2 = 1 := MonoidHom.mem_ker.1 (by rw [hS]; exact Subgroup.mem_top _)
    exact huv (h1.trans h2.symm)

theorem i2_diag_factor {X K J C : Subgroup G} (hC : GLAPComponent 3 X C) (hCK : C ≤ K)
    (hJK : J ≤ K) (hKX : K ≤ X) (hJX : J ≤ X)
    (hdiag : ∀ m ∈ C, ∃ j ∈ J, ∃ n ∈ centModSubgroup 3 C, m = j * n)
    {a : ↥X ⧸ GLAPPrimeCore 3 ↥X} (ha : a ∈ barX 3 X C) :
    ∃ j : ↥J, ∃ c : ↥X ⧸ GLAPPrimeCore 3 ↥X, c ∈ barX 3 X K ∧
      (∀ d ∈ barX 3 X C, d * c = c * d) ∧
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨(j : G), hJX j.2⟩ * c = a := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ha
  have hzC : (z : G) ∈ C := Subgroup.mem_subgroupOf.1 hz
  obtain ⟨j, hj, n, hn, hmn⟩ := hdiag _ hzC
  have hnX_eq : n = (j : G)⁻¹ * (z : G) := by
    rw [hmn]
    group
  have hnX : n ∈ X := by
    rw [hnX_eq]
    exact X.mul_mem (X.inv_mem (hJX hj)) z.2
  have hnK : n ∈ K := by
    rw [hnX_eq]
    exact K.mul_mem (K.inv_mem (hJK hj)) (hCK hzC)
  refine ⟨⟨j, hj⟩, QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨n, hnX⟩, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map.2 ⟨⟨n, hnX⟩, Subgroup.mem_subgroupOf.2 hnK, rfl⟩
  · intro d hd
    exact ((i2_centMod_central Nat.prime_three hC hnX hn) d hd).symm.eq
  · rw [← map_mul]
    congr 1
    exact Subtype.ext hmn.symm

theorem i2_hit_J {X K J C : Subgroup G} {Q : Type} [Group Q]
    (hC : GLAPComponent 3 X C) (hCK : C ≤ K) (hJK : J ≤ K) (hKX : K ≤ X) (hJX : J ≤ X)
    (hdiag : ∀ m ∈ C, ∃ j ∈ J, ∃ n ∈ centModSubgroup 3 C, m = j * n)
    {μ : ↥(barX 3 X K) →* Q} (hμs : Function.Surjective μ)
    (hμk : ∀ k : ↥(barX 3 X K), μ k = 1 ↔
      ∀ d ∈ barX 3 X C, d * (k : ↥X ⧸ GLAPPrimeCore 3 ↥X) = (k : ↥X ⧸ GLAPPrimeCore 3 ↥X) * d)
    (hdec : ∀ y ∈ barX 3 X K, ∃ a ∈ barX 3 X C,
      ∃ n ∈ Subgroup.centralizer (barX 3 X C : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)), y = a * n)
    (hCKb : barX 3 X C ≤ barX 3 X K) (q : Q) :
    ∃ j : ↥J, ∃ hj : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨(j : G), hJX j.2⟩ :
        ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X K, μ ⟨_, hj⟩ = q := by
  obtain ⟨a, ha, hμa⟩ := i2_factor_hit hCKb hdec hμs hμk q
  obtain ⟨j, c, hcK, hcomm, hjc⟩ := i2_diag_factor hC hCK hJK hKX hJX hdiag ha
  have hj : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨(j : G), hJX j.2⟩ :
      ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X K :=
    barX_mono (X := X) 3 hJK
      (Subgroup.mem_map.2 ⟨⟨(j : G), hJX j.2⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩)
  refine ⟨j, hj, ?_⟩
  have hmul : (⟨_, hj⟩ : ↥(barX 3 X K)) * ⟨c, hcK⟩ = ⟨a, hCKb ha⟩ := Subtype.ext hjc
  have hc1 : μ ⟨c, hcK⟩ = 1 := (hμk _).2 hcomm
  have h := congrArg μ hmul
  rw [map_mul, hc1, mul_one, hμa] at h
  exact h

theorem i2_main {X M K J : Subgroup G} {x : G}
    (hM : GLAPComponent 3 X M) (hxX : x ∈ X) (hx3 : x ^ 3 = 1)
    (hMx1 : GLBConj x M ≠ M) (hMx2 : GLBConj x (GLBConj x M) ≠ M)
    (hKeq : K = M ⊔ GLBConj x M ⊔ GLBConj x (GLBConj x M))
    (hJK : J ≤ K) (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    ∃ φ : PSimple 3 K ≃* (PSimple 3 M × PSimple 3 M × PSimple 3 M),
      ∃ ψ₁ ψ₂ ψ₃ : PSimple 3 J ≃* PSimple 3 M, ∀ j : ↥J,
        φ (QuotientGroup.mk (QuotientGroup.mk (⟨(j : G), hJK j.2⟩ : ↥K))) =
          (ψ₁ (QuotientGroup.mk (QuotientGroup.mk j)), ψ₂ (QuotientGroup.mk (QuotientGroup.mk j)),
            ψ₃ (QuotientGroup.mk (QuotientGroup.mk j))) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hMx1 (gLBConj_one M)
  have hC1 : GLAPComponent 3 X (GLBConj x M) :=
    i2Fam_comp hM hxX (GLBConj x M) (by simp [i2Fam])
  have hC2 : GLAPComponent 3 X (GLBConj x (GLBConj x M)) :=
    i2Fam_comp hM hxX (GLBConj x (GLBConj x M)) (by simp [i2Fam])
  have hMX : M ≤ X := hM.1
  have hAX : M ⊔ GLBConj x M ≤ X := sup_le hMX hC1.1
  have hKX : K ≤ X := by
    rw [hKeq]
    exact sup_le hAX hC2.1
  have hJX : J ≤ X := hJK.trans hKX
  have hMK : M ≤ K := by
    rw [hKeq]
    exact le_sup_of_le_left le_sup_left
  have hM1K : GLBConj x M ≤ K := by
    rw [hKeq]
    exact le_sup_of_le_left le_sup_right
  have hM2K : GLBConj x (GLBConj x M) ≤ K := by
    rw [hKeq]
    exact le_sup_right
  have hn01 : M ≠ GLBConj x M := fun h => hMx1 h.symm
  have hn02 : M ≠ GLBConj x (GLBConj x M) := fun h => hMx2 h.symm
  have hxxx : x * (x * x) = 1 := by
    rw [← hx3, pow_three]
  have h3 : GLBConj x (GLBConj x (GLBConj x M)) = M := by
    rw [gLBConj_gLBConj, gLBConj_gLBConj, hxxx, gLBConj_one]
  have hn12 : GLBConj x M ≠ GLBConj x (GLBConj x M) := by
    intro h
    apply hMx2
    have h' := congrArg (GLBConj x) h
    rw [h3] at h'
    exact h'
  have hc01 := i2_commute_of_bot (idiag_barX_commute hM hC1 hn01)
  have hc02 := i2_commute_of_bot (idiag_barX_commute hM hC2 hn02)
  have hc12 := i2_commute_of_bot (idiag_barX_commute hC1 hC2 hn12)
  have hKb : barX 3 X K =
      barX 3 X M ⊔ barX 3 X (GLBConj x M) ⊔ barX 3 X (GLBConj x (GLBConj x M)) := by
    rw [hKeq, i183_barX_sup hAX hC2.1, i183_barX_sup hMX hC1.1]
  have hD0K : barX 3 X M ≤ barX 3 X K := barX_mono 3 hMK
  have hD1K : barX 3 X (GLBConj x M) ≤ barX 3 X K := barX_mono 3 hM1K
  have hD2K : barX 3 X (GLBConj x (GLBConj x M)) ≤ barX 3 X K := barX_mono 3 hM2K
  have hdec0 : ∀ y ∈ barX 3 X K, ∃ a ∈ barX 3 X M,
      ∃ n ∈ Subgroup.centralizer (barX 3 X M : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)), y = a * n :=
    fun y hy => i2_dec_zero hc01 hc02 hc12 (by rw [← hKb]; exact hy)
  have hdec1 : ∀ y ∈ barX 3 X K, ∃ a ∈ barX 3 X (GLBConj x M),
      ∃ n ∈ Subgroup.centralizer (barX 3 X (GLBConj x M) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)),
        y = a * n :=
    fun y hy => i2_dec_one hc01 hc02 hc12 (by rw [← hKb]; exact hy)
  have hdec2 : ∀ y ∈ barX 3 X K, ∃ a ∈ barX 3 X (GLBConj x (GLBConj x M)),
      ∃ n ∈ Subgroup.centralizer (barX 3 X (GLBConj x (GLBConj x M)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)), y = a * n :=
    fun y hy => i2_dec_two hc01 hc02 hc12 (by rw [← hKb]; exact hy)
  obtain ⟨n0, n1, n2⟩ := i2_normal_factors hc01 hc02 hc12
  have hn0 : ∀ g ∈ barX 3 X K, ∀ d ∈ barX 3 X M, g * d * g⁻¹ ∈ barX 3 X M :=
    fun g hg => n0 g (by rw [← hKb]; exact hg)
  have hn1 : ∀ g ∈ barX 3 X K, ∀ d ∈ barX 3 X (GLBConj x M),
      g * d * g⁻¹ ∈ barX 3 X (GLBConj x M) :=
    fun g hg => n1 g (by rw [← hKb]; exact hg)
  have hn2 : ∀ g ∈ barX 3 X K, ∀ d ∈ barX 3 X (GLBConj x (GLBConj x M)),
      g * d * g⁻¹ ∈ barX 3 X (GLBConj x (GLBConj x M)) :=
    fun g hg => n2 g (by rw [← hKb]; exact hg)
  have θ0 : (↥(barX 3 X M) ⧸ Subgroup.center ↥(barX 3 X M)) ≃* PSimple 3 M :=
    (i2_psimple_barX hM).symm
  have θ1 : (↥(barX 3 X (GLBConj x M)) ⧸ Subgroup.center ↥(barX 3 X (GLBConj x M))) ≃*
      PSimple 3 M :=
    (i2_psimple_barX hC1).symm.trans (i2_psimple_conj x M).symm
  have θ2 : (↥(barX 3 X (GLBConj x (GLBConj x M))) ⧸
      Subgroup.center ↥(barX 3 X (GLBConj x (GLBConj x M)))) ≃* PSimple 3 M :=
    (i2_psimple_barX hC2).symm.trans
      ((i2_psimple_conj x (GLBConj x M)).symm.trans (i2_psimple_conj x M).symm)
  have hcl := i2_psimple_centreless hM
  haveI hQnt : Nontrivial (PSimple 3 M) := i2_psimple_nontrivial hM
  obtain ⟨μ0, μ1, μ2, hk0, hk1, hk2, hs0, hs1, hs2, hΛs, hcen_of, hcen_to⟩ :=
    i2_Kb_stage hc01 hc02 hc12 hKb hD0K hD1K hD2K θ0 θ1 θ2 hcl
  have hcopK : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  obtain ⟨fK, hfK⟩ : ∃ f : ↥K →* (↥X ⧸ GLAPPrimeCore 3 ↥X),
      f = (barX 3 X K).subtype.comp (barMap 3 hKX) := ⟨_, rfl⟩
  have hfK_apply : ∀ k : ↥K, fK k =
      ((barMap 3 hKX k : ↥(barX 3 X K)) : ↥X ⧸ GLAPPrimeCore 3 ↥X) := fun k => by
    rw [hfK]
    rfl
  have hfK_surj : ∀ y ∈ barX 3 X K, ∃ k : ↥K, fK k = y := by
    intro y hy
    obtain ⟨k, hk⟩ := barMap_surjective hKX (⟨y, hy⟩ : ↥(barX 3 X K))
    exact ⟨k, (hfK_apply k).trans (congrArg Subtype.val hk)⟩
  obtain ⟨NY, hNY⟩ : ∃ S : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X),
      S = (GLAPPrimeCore 3 ↥K).map fK := ⟨_, rfl⟩
  have hNY_mem : ∀ k ∈ GLAPPrimeCore 3 ↥K, fK k ∈ NY := fun k hk => by
    rw [hNY]
    exact Subgroup.mem_map.2 ⟨k, hk, rfl⟩
  have hNY_le : NY ≤ barX 3 X K := by
    intro y hy
    rw [hNY] at hy
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hy
    rw [hfK_apply]
    exact (barMap 3 hKX k).2
  have hNY_normal : ∀ g ∈ barX 3 X K, ∀ n ∈ NY, g * n * g⁻¹ ∈ NY := by
    intro g hg n hn
    rw [hNY] at hn ⊢
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨k, rfl⟩ := hfK_surj g hg
    refine Subgroup.mem_map.2 ⟨k * m * k⁻¹, (GLAPPrimeCore.normal 3 ↥K).conj_mem m hm k, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hcopNY : Nat.Coprime 3 (Nat.card NY) := by
    rw [hNY]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (GLAPPrimeCore 3 ↥K) fK) hcopK
  have hN0 : NY ⊓ barX 3 X M = ⊥ :=
    i2_inf_bot hD0K hNY_normal hcopNY (i2_core_barX_eq_bot hM)
  have hN1 : NY ⊓ barX 3 X (GLBConj x M) = ⊥ :=
    i2_inf_bot hD1K hNY_normal hcopNY (i2_core_barX_eq_bot hC1)
  have hN2 : NY ⊓ barX 3 X (GLBConj x (GLBConj x M)) = ⊥ :=
    i2_inf_bot hD2K hNY_normal hcopNY (i2_core_barX_eq_bot hC2)
  have hNc' : ∀ n ∈ GLAPPrimeCore 3 ↥K, ∀ g ∈ barX 3 X K, g * fK n = fK n * g := fun n hn =>
    i2_central_of_normal hc01 hc02 hc12 hKb hn0 hn1 hn2 hD0K hD1K hD2K hNY_normal hNY_le
      hN0 hN1 hN2 (hNY_mem n hn)
  have hNc : ∀ n ∈ GLAPPrimeCore 3 ↥K, ∀ g : ↥(barX 3 X K),
      g * barMap 3 hKX n = barMap 3 hKX n * g := by
    intro n hn g
    apply Subtype.ext
    show g.1 * ((barMap 3 hKX n : ↥(barX 3 X K)) : ↥X ⧸ GLAPPrimeCore 3 ↥X) =
      ((barMap 3 hKX n : ↥(barX 3 X K)) : ↥X ⧸ GLAPPrimeCore 3 ↥X) * g.1
    rw [← hfK_apply]
    exact hNc' n hn g.1 g.2
  have hΛK : Function.Surjective (μ0.prod (μ1.prod μ2)) := hΛs
  have hcen_of' : ∀ k : ↥(barX 3 X K), (μ0.prod (μ1.prod μ2)) k = 1 →
      ∀ g : ↥(barX 3 X K), g * k = k * g := by
    intro k hk g
    have h0 : μ0 k = 1 := congrArg Prod.fst hk
    have h12 : (μ1.prod μ2) k = 1 := congrArg Prod.snd hk
    have h1 : μ1 k = 1 := congrArg Prod.fst h12
    have h2 : μ2 k = 1 := congrArg Prod.snd h12
    exact Subtype.ext (hcen_of k h0 h1 h2 g.1 g.2)
  have hcen_to' : ∀ z : ↥(barX 3 X K), (∀ g : ↥(barX 3 X K), g * z = z * g) →
      (μ0.prod (μ1.prod μ2)) z = 1 := by
    intro z hz
    obtain ⟨h0, h1, h2⟩ := hcen_to z hz
    show (μ0 z, μ1 z, μ2 z) = 1
    rw [h0, h1, h2]
    all_goals rfl
  obtain ⟨eK, heK⟩ := i2_K_abstract (GLAPPrimeCore 3 ↥K) (barMap 3 hKX) (barMap_surjective hKX)
    (i2_ker_barMap_le_core hKX) hΛK (i2_prod3_centreless hcl) hcen_of' hcen_to' hNc
  have hDJK : barX 3 X J ≤ barX 3 X K := barX_mono 3 hJK
  obtain ⟨hJbar, hGq, hdiagAll⟩ := i2_J_part hM hxX hx3 hx1 hMx1 hMx2 hKeq hJK hJ
  have hDJq : CFSG.Open.IsQuasisimple ↥(barX 3 X J) := by
    rw [hJbar]
    exact hGq
  have hdiag0 : ∀ m ∈ M, ∃ j ∈ J, ∃ n ∈ centModSubgroup 3 M, m = j * n :=
    hdiagAll M (by simp [i2Fam])
  have hdiag1 : ∀ m ∈ GLBConj x M, ∃ j ∈ J, ∃ n ∈ centModSubgroup 3 (GLBConj x M), m = j * n :=
    hdiagAll (GLBConj x M) (by simp [i2Fam])
  have hdiag2 : ∀ m ∈ GLBConj x (GLBConj x M),
      ∃ j ∈ J, ∃ n ∈ centModSubgroup 3 (GLBConj x (GLBConj x M)), m = j * n :=
    hdiagAll (GLBConj x (GLBConj x M)) (by simp [i2Fam])
  have hNJtop : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
    intro htop
    haveI : Nontrivial ↥(barX 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) J) :=
      Quasisimple.nontrivial hJ.2.2.1.2.2
    obtain ⟨u, v, huv⟩ := exists_pair_ne ↥(barX 3 (K ⊓ Subgroup.centralizer ({x} : Set G)) J)
    have e := quotEquivBarX Nat.prime_three hJ.1 hJ.2.1
    have hall : ∀ w : ↥J ⧸ GLAPPrimeCore 3 ↥J, w = 1 := by
      intro w
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
      exact (QuotientGroup.eq_one_iff j).2 (by rw [htop]; exact Subgroup.mem_top j)
    apply huv
    have hu : u = 1 := by
      have h := congrArg e (hall (e.symm u))
      rw [map_one, MulEquiv.apply_symm_apply] at h
      exact h
    have hv : v = 1 := by
      have h := congrArg e (hall (e.symm v))
      rw [map_one, MulEquiv.apply_symm_apply] at h
      exact h
    rw [hu, hv]
  have hψ0 : Function.Surjective ((μ0.comp (Subgroup.inclusion hDJK)).comp (barMap 3 hJX)) := by
    intro q
    obtain ⟨j, _, hq⟩ := i2_hit_J hM hMK hJK hKX hJX hdiag0 hs0 hk0 hdec0 hD0K q
    exact ⟨j, hq⟩
  have hψ1 : Function.Surjective ((μ1.comp (Subgroup.inclusion hDJK)).comp (barMap 3 hJX)) := by
    intro q
    obtain ⟨j, _, hq⟩ := i2_hit_J hC1 hM1K hJK hKX hJX hdiag1 hs1 hk1 hdec1 hD1K q
    exact ⟨j, hq⟩
  have hψ2 : Function.Surjective ((μ2.comp (Subgroup.inclusion hDJK)).comp (barMap 3 hJX)) := by
    intro q
    obtain ⟨j, _, hq⟩ := i2_hit_J hC2 hM2K hJK hKX hJX hdiag2 hs2 hk2 hdec2 hD2K q
    exact ⟨j, hq⟩
  have hψ0' : Function.Surjective (μ0.comp (Subgroup.inclusion hDJK)) := by
    intro q
    obtain ⟨j, hj⟩ := hψ0 q
    exact ⟨barMap 3 hJX j, hj⟩
  have hψ1' : Function.Surjective (μ1.comp (Subgroup.inclusion hDJK)) := by
    intro q
    obtain ⟨j, hj⟩ := hψ1 q
    exact ⟨barMap 3 hJX j, hj⟩
  have hψ2' : Function.Surjective (μ2.comp (Subgroup.inclusion hDJK)) := by
    intro q
    obtain ⟨j, hj⟩ := hψ2 q
    exact ⟨barMap 3 hJX j, hj⟩
  obtain ⟨hn0J, hker0J⟩ := i2_J_abstract (GLAPPrimeCore 3 ↥J) (barMap 3 hJX)
    (barMap_surjective hJX) (i2_ker_barMap_le_core hJX) hDJq hNJtop _ hψ0' hcl hQnt
  obtain ⟨hn1J, hker1J⟩ := i2_J_abstract (GLAPPrimeCore 3 ↥J) (barMap 3 hJX)
    (barMap_surjective hJX) (i2_ker_barMap_le_core hJX) hDJq hNJtop _ hψ1' hcl hQnt
  obtain ⟨hn2J, hker2J⟩ := i2_J_abstract (GLAPPrimeCore 3 ↥J) (barMap 3 hJX)
    (barMap_surjective hJX) (i2_ker_barMap_le_core hJX) hDJq hNJtop _ hψ2' hcl hQnt
  obtain ⟨e0, he0⟩ := i2_quot_centre_equiv (GLAPPrimeCore 3 ↥J) _ hψ0 hcl
    (by
      intro n hn
      exact MonoidHom.mem_ker.2 (hn0J n hn))
    (fun k hk k' => hker0J k hk k')
  obtain ⟨e1, he1⟩ := i2_quot_centre_equiv (GLAPPrimeCore 3 ↥J) _ hψ1 hcl
    (by
      intro n hn
      exact MonoidHom.mem_ker.2 (hn1J n hn))
    (fun k hk k' => hker1J k hk k')
  obtain ⟨e2, he2⟩ := i2_quot_centre_equiv (GLAPPrimeCore 3 ↥J) _ hψ2 hcl
    (by
      intro n hn
      exact MonoidHom.mem_ker.2 (hn2J n hn))
    (fun k hk k' => hker2J k hk k')
  refine ⟨eK, e0, e1, e2, fun j => ?_⟩
  rw [heK, he0 j, he1 j, he2 j]
  all_goals rfl

end Assembly

theorem i2ProdAt_holds (G : Type) [Group G] [Finite G] : I2ProdAt G := by
  unfold I2ProdAt
  intro a x M K J hM h1 h2 hK hxX hx3 hJK hJ
  exact i2_main hM hxX hx3 h1 h2 hK hJK hJ

end CFSG.LocalAnalysis.GLTheoremA
