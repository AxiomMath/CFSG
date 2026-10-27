module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29H
public import CFSG.GH74.Generic.BProg.B2.Lemma82Gen
public import CFSG.GH74.Generic.BProg.B3.S3T2L291A

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  Subgroup CFSG.GH74.Generic.BProg.B1.PilotS3
open scoped commutatorElement

namespace S3T2L291

variable {G : Type} [Group G] [Finite G]

theorem comm_eq_bot_of_hyperplanes {P E₁ : Subgroup G} {d : G} (hP : oPrimeResidualOf 2 P = P)
    (hE₁ : CFSG.IsElementaryAbelian 2 ↥E₁) (hr : 2 ≤ pRank 2 ↥E₁)
    (hE₁d : E₁ ≤ centralizer ({d} : Set G)) (hPd : P ≤ centralizer ({d} : Set G))
    (hPE₁ : P ≤ centralizer (E₁ : Set G))
    (h2C : ∀ b ∈ E₁, b ≠ 1 → ⁅P, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓
      centralizer ({b} : Set G)⁆ ≤ pPrimeCoreOf 2 (centralizer ({b} : Set G)))
    (hB : ∀ b ∈ E₁, b ≠ 1 → ⁅P, pPrimeCoreOf 2 (centralizer ({b} : Set G))⁆ = ⊥) :
    ⁅P, pPrimeCoreOf 2 (centralizer ({d} : Set G))⁆ = ⊥ := by
  set Y : Subgroup G := pPrimeCoreOf 2 (centralizer ({d} : Set G)) with hY
  have hYodd : Odd (Nat.card ↥Y) := TwoThin.card_pPrimeCoreOf_odd _
  have hNY : ∀ g ∈ centralizer ({d} : Set G), g ∈ normalizer (Y : Set G) := fun g hg =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hg)
  have hW : ∀ b ∈ E₁, b ≠ 1 → ⁅P, Y ⊓ centralizer ({b} : Set G)⁆ = ⊥ := by
    intro b hb hb1
    have hPb : P ≤ centralizer ({b} : Set G) := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 (hPE₁ hg) b hb).symm)
    have hPW : P ≤ normalizer ((Y ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G) :=
      fun g hg => TwoThin.mem_normalizer_inf (hNY g (hPd hg)) (Subgroup.le_normalizer (hPb hg))
    have hWodd : Nat.Coprime 2 (Nat.card ↥(Y ⊓ centralizer ({b} : Set G))) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (Nat.coprime_two_left.2 hYodd)
    have h1 := commutator_le_commutator_commutator_of_oPrimeResidual hPW hWodd hP
    rw [commutator_comm (Y ⊓ centralizer ({b} : Set G)) P] at h1
    have h2 : ⁅⁅P, Y ⊓ centralizer ({b} : Set G)⁆, P⁆ = ⊥ := by
      rw [eq_bot_iff, commutator_comm]
      exact (commutator_mono le_rfl (h2C b hb hb1)).trans (hB b hb hb1).le
    rw [h2] at h1
    exact le_bot_iff.1 h1
  have hgen := B2.le_iSup_centralizer_hyperplanes hE₁ hr (fun e he => hNY e (hE₁d he)) hYodd
  have hYC : Y ≤ centralizer (P : Set G) := by
    refine hgen.trans (iSup_le fun F => iSup_le fun hFE => iSup_le fun hFr => ?_)
    have hF1 : F ≠ ⊥ := by
      intro hbot
      rw [hbot, C3.Layer1.Back.pRank_bot_eq_zero] at hFr
      omega
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
    have hbY : Y ⊓ centralizer (F : Set G) ≤ Y ⊓ centralizer ({(b : G)} : Set G) :=
      inf_le_inf_left Y (Subgroup.centralizer_le (Set.singleton_subset_iff.2 b.2))
    have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
    refine hbY.trans ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hW b (hFE b.2) hb1'
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, commutator_comm] at hYC
  exact hYC

omit [Finite G] in
theorem exists_mem_ne_one_of_le_sup {x : G} {E E₁ : Subgroup G} (hx2 : x * x = 1)
    (hEx : ∀ h ∈ E, h * x = x * h) (hE₁A : E₁ ≤ E ⊔ zpowers x)
    (hE₁el : CFSG.IsElementaryAbelian 2 ↥E₁) (hcard : 2 < Nat.card ↥E₁) :
    ∃ e ∈ E₁, e ≠ 1 ∧ e ∈ E := by
  classical
  by_contra hno
  push Not at hno
  have hsq : ∀ h ∈ E₁, h * h = 1 := fun h hh => by
    rw [← sq]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E₁) h hh
  have hone : ∀ h ∈ E₁, h ∈ E → h = 1 := fun h hh hhE => by
    by_contra h1
    exact hno h hh h1 hhE
  have hinj : Function.Injective (fun b : ↥E₁ => decide ((b : G) ∈ E)) := by
    intro a c hac
    simp only [decide_eq_decide] at hac
    apply Subtype.ext
    by_cases haE : (a : G) ∈ E
    · rw [hone a a.2 haE, hone c c.2 (hac.1 haE)]
    · have hcE : (c : G) ∉ E := fun h => haE (hac.2 h)
      obtain ⟨ea, hea, ha' | ha'⟩ := S3Sec29H.mem_sup_zpowers hx2 hEx (hE₁A a.2)
      · exact (haE (ha' ▸ hea)).elim
      obtain ⟨ec, hec, hc' | hc'⟩ := S3Sec29H.mem_sup_zpowers hx2 hEx (hE₁A c.2)
      · exact (hcE (hc' ▸ hec)).elim
      have e1 : ea * x * (ec * x) = ea * ec * (x * x) := by
        have := hEx ec hec
        calc ea * x * (ec * x) = ea * (x * ec) * x := by group
          _ = ea * (ec * x) * x := by rw [this]
          _ = ea * ec * (x * x) := by group
      have hac1 : (a : G) * c = 1 := by
        refine hone _ (E₁.mul_mem a.2 c.2) ?_
        rw [ha', hc', e1, hx2, mul_one]
        exact E.mul_mem hea hec
      calc (a : G) = a * (c * c) := by rw [hsq c c.2, mul_one]
        _ = (a * c) * c := by group
        _ = c := by rw [hac1, one_mul]
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  omega

theorem comm_of_semisimple {x : G} {K A E E₁ P : Subgroup G} (hx : orderOf x = 2)
    (hKx : K ≤ centralizer ({x} : Set G)) (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x)
    (hE₁A : E₁ ≤ A) (hE₁el : CFSG.IsElementaryAbelian 2 ↥E₁) (hr : 2 ≤ pRank 2 ↥E₁)
    (hPx : P ≤ centralizer ({x} : Set G)) (hPE₁ : P ≤ centralizer (E₁ : Set G))
    (hlift : ∀ e ∈ E, e ≠ 1 → (e ∈ E₁ ∨ e * x ∈ E₁) → P ≤ centralizer ({e} : Set G) →
      P ≤ liftAt x e (Lbar x e K))
    (hall : ∀ e ∈ E, e ≠ 1 → NbhdSemisimple x e (Lbar x e K)) :
    ∀ b ∈ E₁, b ≠ 1 → ⁅P, pPrimeCoreOf 2 (centralizer ({b} : Set G))⁆ = ⊥ := by
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hEx : ∀ h ∈ E, h * x = x * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKx (hEK hh))
  have hPb : ∀ b ∈ E₁, P ≤ centralizer ({b} : Set G) := fun b hb g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 (hPE₁ hg) b hb).symm)
  have hss : ∀ e ∈ E, e ≠ 1 → (e ∈ E₁ ∨ e * x ∈ E₁) → P ≤ centralizer ({e} : Set G) →
      ∀ d₁ ∈ closure ({x, e} : Set G), d₁ ≠ 1 →
        ⁅P, pPrimeCoreOf 2 (centralizer ({d₁} : Set G))⁆ = ⊥ :=
    fun e he he1 heE₁ hPe d₁ hd₁ hd₁1 => le_bot_iff.1
      ((commutator_mono (hlift e he he1 heE₁ hPe) le_rfl).trans (hall e he he1 d₁ hd₁ hd₁1).le)
  have hxe : ∀ e : G, x ∈ closure ({x, e} : Set G) := fun e => subset_closure (by simp)
  have hex : ∀ e : G, e ∈ closure ({x, e} : Set G) := fun e => subset_closure (by simp)
  intro b hb hb1
  rw [hAE] at hE₁A
  obtain ⟨e, he, hbe | hbe⟩ := S3Sec29H.mem_sup_zpowers hx2 hEx (hE₁A hb)
  · rw [hbe] at hb hb1 ⊢
    exact hss e he hb1 (Or.inl hb) (hPb e hb) e (hex e) hb1
  by_cases he1 : e = 1
  ·
    rw [hbe, he1, one_mul] at hb1 ⊢
    have hcard : 2 < Nat.card ↥E₁ := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hE₁el]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ pRank 2 ↥E₁ := Nat.pow_le_pow_right (by norm_num) hr
    obtain ⟨e', he'E₁, he'1, he'E⟩ := exists_mem_ne_one_of_le_sup hx2 hEx hE₁A hE₁el hcard
    exact hss e' he'E he'1 (Or.inl he'E₁) (hPb e' he'E₁) x (hxe e') hb1
  ·
    rw [hbe] at hb hb1 ⊢
    have hPe : P ≤ centralizer ({e} : Set G) := by
      intro g hg
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hPb (e * x) hb hg)
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 (hPx hg)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * e = g * (e * x) * x := by rw [mul_assoc, mul_assoc, hx2, mul_one]
        _ = e * x * (g * x) := by rw [h1, mul_assoc]
        _ = e * x * (x * g) := by rw [h2]
        _ = e * g := by rw [mul_assoc, ← mul_assoc x, hx2, one_mul]
    exact hss e he he1 (Or.inr hb) hPe (e * x) (mul_mem (hex e) (hxe e)) hb1

end S3T2L291

end CFSG.GH74.Generic.BProg.B3
