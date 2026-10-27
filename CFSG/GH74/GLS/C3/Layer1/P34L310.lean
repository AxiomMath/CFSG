module

public import CFSG.GH74.GLS.C3.Layer1.P34Proj
public import CFSG.GH74.GLS.C3.Layer1.P34Aux

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T P Q : Subgroup X} {x z f h : X}

omit [Finite X] in
theorem conj_le_closure {B : Subgroup X} (hB : B ≤ closure {v : X | v ∈ B ∧ v * v = 1}) (e : X) :
    conjSubgroup B e ≤ closure {v : X | v ∈ conjSubgroup B e ∧ v * v = 1} := by
  intro b hb
  rw [mem_conjSubgroup_iff] at hb
  have key : ∀ y ∈ closure {v : X | v ∈ B ∧ v * v = 1},
      e⁻¹ * y * e ∈ closure {v : X | v ∈ conjSubgroup B e ∧ v * v = 1} := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem p hp =>
      refine subset_closure ⟨?_, ?_⟩
      · rw [mem_conjSubgroup_iff]
        have e1 : e * (e⁻¹ * p * e) * e⁻¹ = p := by group
        rw [e1]; exact hp.1
      · calc e⁻¹ * p * e * (e⁻¹ * p * e) = e⁻¹ * (p * p) * e := by group
          _ = 1 := by rw [hp.2]; group
    | one => simp
    | mul a b _ _ ha hb =>
      have : e⁻¹ * (a * b) * e = (e⁻¹ * a * e) * (e⁻¹ * b * e) := by group
      rw [this]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : e⁻¹ * a⁻¹ * e = (e⁻¹ * a * e)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ha
  have := key _ (hB hb)
  have e2 : e⁻¹ * (e * b * e⁻¹) * e = b := by group
  rwa [e2] at this

theorem lemma310_core (c : Cfg34 X T P Q x z f h) (hD : DihedralShapeFacts) (hM : DihedralMaxFacts)
    (h38 : Lemma38 T P z) (h39 : Lemma39 T P Q z f) {D : Subgroup X} {g : X} (hDT : D ≤ T)
    (hPD : P ≤ D) (hg : g ∈ normalizer (D : Set X)) (hgodd : Odd (orderOf g))
    (hmove : ∃ a ∈ P, g⁻¹ * a * g ∉ P) : False := by
  obtain ⟨h8, hPp, hPgen, hPz⟩ := hD X P c.P_dihedral
  have hggN : g * g ∈ normalizer (D : Set X) := (normalizer (D : Set X)).mul_mem hg hg
  have h1N : (1 : X) ∈ normalizer (D : Set X) := (normalizer (D : Set X)).one_mem
  have hPeD : ∀ e ∈ normalizer (D : Set X), ∀ b ∈ conjSubgroup P e, b ∈ D := by
    intro e he b hb
    rw [mem_conjSubgroup_iff] at hb
    exact ((Subgroup.mem_normalizer_iff.1 he b).2 (hPD hb))
  have hPeT : ∀ e ∈ normalizer (D : Set X), ∀ b ∈ conjSubgroup P e, b ∈ T :=
    fun e he b hb => hDT (hPeD e he b hb)
  have hPeN : ∀ e ∈ normalizer (D : Set X), ∀ d ∈ D, ∀ b ∈ conjSubgroup P e,
      d * b * d⁻¹ ∈ conjSubgroup P e := by
    intro e he d hd b hb
    rw [mem_conjSubgroup_iff] at hb ⊢
    have h1 : e * d * e⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 he d).1 hd
    have h2 := c.P_norm _ (hDT h1) _ hb
    have e1 : e * (d * b * d⁻¹) * e⁻¹ = (e * d * e⁻¹) * (e * b * e⁻¹) * (e * d * e⁻¹)⁻¹ := by group
    rw [e1]; exact h2
  have hPconjD : ∀ e ∈ normalizer (D : Set X), ∀ a ∈ P, e⁻¹ * a * e ∈ conjSubgroup P e := by
    intro e he a ha
    rw [mem_conjSubgroup_iff]
    have e1 : e * (e⁻¹ * a * e) * e⁻¹ = a := by group
    rw [e1]; exact ha
  have hzfix : ∀ e ∈ normalizer (D : Set X), e⁻¹ * z * e = z := by
    intro e he
    refine h38 e (fun a ha => ?_)
    have := hPeT e he _ (hPconjD e he a ha)
    exact this
  have hconjz : ∀ e : X, ∀ v ∈ conjSubgroup P e, v * v = 1 → v ≠ 1 →
      ∃ g'' : X, g''⁻¹ * z * g'' = v := by
    intro e v hv hv2 hv1
    rw [mem_conjSubgroup_iff] at hv
    have ha2 : (e * v * e⁻¹) * (e * v * e⁻¹) = 1 := by
      calc (e * v * e⁻¹) * (e * v * e⁻¹) = e * (v * v) * e⁻¹ := by group
        _ = 1 := by rw [hv2]; group
    have ha1 : e * v * e⁻¹ ≠ 1 := by
      intro h1
      apply hv1
      calc v = e⁻¹ * (e * v * e⁻¹) * e := by group
        _ = 1 := by rw [h1]; group
    have hord : orderOf (e * v * e⁻¹) = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
    obtain ⟨g', hg'⟩ := c.kf_conj_P _ hv hord
    refine ⟨g' * e, ?_⟩
    calc (g' * e)⁻¹ * z * (g' * e) = e⁻¹ * (g'⁻¹ * z * g') * e := by group
      _ = e⁻¹ * (e * v * e⁻¹) * e := by rw [hg']
      _ = v := by group
  have hinv : ∀ e ∈ normalizer (D : Set X), ∀ v ∈ conjSubgroup P e, v * v = 1 →
      v ∈ P ∨ ∃ r ∈ P ⊔ Q, v = r * h := by
    intro e he v hv hv2
    by_cases hv1 : v = 1
    · left; rw [hv1]; exact P.one_mem
    rcases c.kf_invol v (hPeT e he v hv) hv2 with hRf | ⟨r, hr, hvr⟩
    · left
      exact h39 v (hconjz e v hv hv2 hv1) (hPeT e he v hv) hRf
    · right; exact ⟨r, hr, hvr⟩
  have hgen : ∀ e : X, conjSubgroup P e ≤ closure {v : X | v ∈ conjSubgroup P e ∧ v * v = 1} :=
    fun e => conj_le_closure (fun a ha => hPgen a ha) e
  have hP1 : ¬ conjSubgroup P g ≤ P := by
    intro hle
    obtain ⟨a, ha, hna⟩ := hmove
    apply hna
    apply hle
    rw [mem_conjSubgroup_iff]
    have e1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [e1]; exact ha
  have hgP : g ∈ normalizer (D : Set X) := hg
  rcases c.kf_h with hh | ⟨hhR, hWdih⟩
  ·
    apply hP1
    refine (hgen g).trans ((closure_le P).2 ?_)
    rintro v ⟨hv, hv2⟩
    by_cases hv1 : v = 1
    · rw [hv1]; exact P.one_mem
    rcases hinv g hgP v hv hv2 with h1 | ⟨r, hr, hvr⟩
    · exact h1
    · rw [hh, mul_one] at hvr
      exact h39 v (hconjz g v hv hv2 hv1) (hPeT g hgP v hv) (mem_sup_left (hvr ▸ hr))
  ·
    set W : Subgroup X := P ⊔ zpowers h with hW
    set M₂ : Subgroup X := Q ⊔ W with hM₂
    have hWT : W ≤ T := sup_le c.P_le (zpowers_le.2 c.h_mem)
    have hhR' : h ∉ P ⊔ Q := fun hm => hhR (mem_sup_left hm)
    have hhP : h ∉ P := fun hm => hhR' (mem_sup_left hm)
    have hTP : T ≤ normalizer (P : Set X) := fun t ht => by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha; exact c.P_norm t ht a ha
      · intro ha
        have := c.P_norm t⁻¹ (T.inv_mem ht) _ ha
        simpa [mul_assoc] using this
    have hh2 : orderOf h = 2 := orderOf_eq_prime (by rw [sq]; exact c.h_sq)
      (fun h1 => hhP (h1 ▸ P.one_mem))
    have hcoeW : (W : Set X) = (P : Set X) * (zpowers h : Set X) :=
      Subgroup.coe_mul_of_right_le_normalizer_left P (zpowers h) (zpowers_le.2 (hTP c.h_mem))
    have hPh : P ⊓ zpowers h = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyP, hyh⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hyh
      rw [Subgroup.mem_bot]
      rcases zpow_involution_cases c.h_sq k with hk | hk
      · exact hk
      · exfalso; rw [hk] at hyP; exact hhP hyP
    have hWcard : Nat.card ↥W = Nat.card ↥P * 2 := by
      have h1 := card_mul_inf P (zpowers h)
      rw [hPh, Subgroup.card_bot, mul_one, Nat.card_zpowers, hh2] at h1
      have h2 : Nat.card ↥((P : Set X) * (zpowers h : Set X)) = Nat.card ↥W := by
        rw [← hcoeW]; rfl
      rw [h2] at h1
      exact h1
    have hinfQW : Q ⊓ W = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyQ, hyW⟩
      have hyW' : y ∈ (W : Set X) := hyW
      rw [hcoeW] at hyW'
      obtain ⟨p, hp, hk, hhk, hy⟩ := hyW'
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hhk
      have hy' : p * h ^ k = y := hy
      rw [Subgroup.mem_bot]
      rcases zpow_involution_cases c.h_sq k with hk1 | hk1
      · rw [hk1, mul_one] at hy'
        have : y ∈ P ⊓ Q := ⟨hy' ▸ hp, hyQ⟩
        rw [c.PQ_inf, Subgroup.mem_bot] at this
        exact this
      · exfalso
        rw [hk1] at hy'
        apply hhR'
        have := (P ⊔ Q).mul_mem ((P ⊔ Q).inv_mem (mem_sup_left hp)) (mem_sup_right hyQ)
        rw [← hy'] at this
        simpa using this
    have hQW : ∀ w ∈ W, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q := fun w hw q hq => c.Q_norm w (hWT hw) q hq
    obtain ⟨π, hπW, hπid, hπker, hπdec⟩ := exists_retraction hQW hinfQW
    have hPW : P ≤ W := le_sup_left
    have hWM : W ≤ M₂ := le_sup_right
    have hQM : Q ≤ M₂ := le_sup_left
    have hPM : P ≤ M₂ := hPW.trans hWM
    have hRM : P ⊔ Q ≤ M₂ := sup_le hPM hQM
    have hhW : h ∈ W := mem_sup_right (mem_zpowers h)
    have hW16 : 16 ≤ Nat.card ↥W := by rw [hWcard]; omega
    have hPeM : ∀ e ∈ normalizer (D : Set X), conjSubgroup P e ≤ M₂ := by
      intro e he
      refine (hgen e).trans ((closure_le _).2 ?_)
      rintro v ⟨hv, hv2⟩
      rcases hinv e he v hv hv2 with h1 | ⟨r, hr, hvr⟩
      · exact hPM h1
      · rw [hvr]; exact M₂.mul_mem (hRM hr) (hWM hhW)
    have hPeQ : ∀ e ∈ normalizer (D : Set X), conjSubgroup P e ⊓ Q = ⊥ := by
      intro e he
      by_contra hne
      have hpe2 : IsPGroup 2 ↥(conjSubgroup P e) :=
        c.T_pgroup.to_le (show conjSubgroup P e ≤ T from fun b hb => hPeT e he b hb)
      obtain ⟨n, hn, hn1, hncent⟩ := exists_central_of_normal (W := conjSubgroup P e) hpe2
        (N := conjSubgroup P e ⊓ Q) inf_le_left
        (fun w hw n hn => ⟨(conjSubgroup P e).mul_mem ((conjSubgroup P e).mul_mem hw hn.1)
          ((conjSubgroup P e).inv_mem hw), c.Q_norm w (hPeT e he w hw) n hn.2⟩) hne
      obtain ⟨-, -, hu⟩ := c.conj_basic e
      rcases hu n hn.1 hncent with h1 | h1
      · exact hn1 h1
      · rw [hzfix e he] at h1
        have : z ∈ P ⊓ Q := ⟨c.z_mem, h1 ▸ hn.2⟩
        rw [c.PQ_inf, Subgroup.mem_bot] at this
        exact c.z_ne_one this
    have hπinj : ∀ e ∈ normalizer (D : Set X), ∀ y y' : ↥M₂, (y : X) ∈ conjSubgroup P e →
        (y' : X) ∈ conjSubgroup P e → π y = π y' → y = y' := by
      intro e he y y' hy hy' hyy'
      have h1 : π (y⁻¹ * y') = 1 := by rw [map_mul, map_inv, hyy']; simp
      have h2 : ((y⁻¹ * y' : ↥M₂) : X) ∈ Q := (hπker _).1 h1
      have h3 : ((y⁻¹ * y' : ↥M₂) : X) ∈ conjSubgroup P e ⊓ Q :=
        ⟨(conjSubgroup P e).mul_mem ((conjSubgroup P e).inv_mem hy) hy', h2⟩
      rw [hPeQ e he, Subgroup.mem_bot] at h3
      exact inv_mul_eq_one.1 (Subtype.ext h3)
    have hP1M : conjSubgroup P g ≤ M₂ := hPeM g hgP
    have hP2M : conjSubgroup P (g * g) ≤ M₂ := hPeM (g * g) hggN
    have hA1W : Aof π (conjSubgroup P g) ≤ W := by
      intro y hy
      obtain ⟨b, -, rfl⟩ := mem_Aof.1 hy
      exact hπW b
    have hA2W : Aof π (conjSubgroup P (g * g)) ≤ W := by
      intro y hy
      obtain ⟨b, -, rfl⟩ := mem_Aof.1 hy
      exact hπW b
    have hA1card : Nat.card ↥(Aof π (conjSubgroup P g)) = Nat.card ↥P :=
      (card_Aof_of_inj π hP1M (hπinj g hgP)).trans (card_conjSubgroup P g)
    have hA2card : Nat.card ↥(Aof π (conjSubgroup P (g * g))) = Nat.card ↥P :=
      (card_Aof_of_inj π hP2M (hπinj (g * g) hggN)).trans (card_conjSubgroup P (g * g))
    have hA1dih : IsDihedralGE8 (Aof π (conjSubgroup P g)) :=
      isDihedralGE8_Aof π hP1M (hπinj g hgP) (isDihedralGE8_conj c.P_dihedral g)
    have hA2dih : IsDihedralGE8 (Aof π (conjSubgroup P (g * g))) :=
      isDihedralGE8_Aof π hP2M (hπinj (g * g) hggN) (isDihedralGE8_conj c.P_dihedral (g * g))
    have hAP : Aof π P = P := by
      ext y
      constructor
      · intro hy
        obtain ⟨b, hb, rfl⟩ := mem_Aof.1 hy
        rw [hπid b (hPW hb)]; exact hb
      · intro hy
        exact mem_Aof.2 ⟨⟨y, hPM hy⟩, hy, hπid ⟨y, hPM hy⟩ (hPW hy)⟩
    have hNotP : ∀ e ∈ normalizer (D : Set X), ¬ conjSubgroup P e ≤ P →
        Aof π (conjSubgroup P e) ≠ P := by
      intro e he hnot hA
      apply hnot
      refine (hgen e).trans ((closure_le P).2 ?_)
      rintro v ⟨hv, hv2⟩
      by_cases hv1 : v = 1
      · rw [hv1]; exact P.one_mem
      have hvM : v ∈ M₂ := hPeM e he hv
      have hπv : π ⟨v, hvM⟩ ∈ P := by
        rw [← hA]; exact mem_Aof.2 ⟨⟨v, hvM⟩, hv, rfl⟩
      have hdec := hπdec ⟨v, hvM⟩
      have hvR : v ∈ P ⊔ Q := by
        have e1 : v = (π ⟨v, hvM⟩) * ((π ⟨v, hvM⟩)⁻¹ * v) := by group
        rw [e1]
        exact (P ⊔ Q).mul_mem (mem_sup_left hπv) (mem_sup_right hdec)
      exact h39 v (hconjz e v hv hv2 hv1) (hPeT e he v hv) (mem_sup_left hvR)
    have hP2 : ¬ conjSubgroup P (g * g) ≤ P := by
      intro hle
      have hN : g * g ∈ normalizer (P : Set X) :=
        mem_normalizer_of_conj_le (fun a ha => hle (hPconjD (g * g) hggN a ha))
      obtain ⟨j, hj⟩ := hgodd
      have hg1 : g ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one g
      have hgeq : g = (g * g) ^ (j + 1) := by
        rw [← sq, ← pow_mul]
        calc g = g ^ (2 * j + 1) * g := by rw [hg1, one_mul]
          _ = g ^ (2 * (j + 1)) := by rw [← pow_succ]; congr 1
      have hgN' : g ∈ normalizer (P : Set X) := by
        rw [hgeq]; exact (normalizer (P : Set X)).pow_mem hN (j + 1)
      apply hP1
      intro b hb
      rw [mem_conjSubgroup_iff] at hb
      exact (Subgroup.mem_normalizer_iff.1 hgN' b).2 hb
    have hA1P : Aof π (conjSubgroup P g) ≠ P := hNotP g hgP hP1
    have hA2P : Aof π (conjSubgroup P (g * g)) ≠ P := hNotP (g * g) hggN hP2
    obtain ⟨hM1, hM2⟩ := hM X W hWdih hW16
    have hPcard2 : Nat.card ↥P * 2 = Nat.card ↥W := hWcard.symm
    have hA1card2 : Nat.card ↥(Aof π (conjSubgroup P g)) * 2 = Nat.card ↥W := by
      rw [hA1card]; exact hPcard2
    have hA2card2 : Nat.card ↥(Aof π (conjSubgroup P (g * g))) * 2 = Nat.card ↥W := by
      rw [hA2card]; exact hPcard2
    have hA12 : Aof π (conjSubgroup P g) = Aof π (conjSubgroup P (g * g)) := by
      rcases hM1 P _ _ hPW hA1W hA2W c.P_dihedral hA1dih hA2dih hPcard2 hA1card2 hA2card2 with
        h1 | h1 | h1
      · exact absurd h1.symm hA1P
      · exact h1
      · exact absurd h1.symm hA2P
    obtain ⟨hI1, hI2⟩ := hM2 P _ hPW hA1W c.P_dihedral hA1dih hPcard2 hA1card2 hA1P.symm
    have hPP1M : P ⊓ conjSubgroup P g ≤ M₂ := inf_le_left.trans hPM
    have hinc : P ⊓ Aof π (conjSubgroup P g) ≤ Aof π (P ⊓ conjSubgroup P g) := by
      refine hI2.trans ?_
      refine Subgroup.commutator_le.2 (fun p hp a ha => ?_)
      obtain ⟨b₁, hb₁, rfl⟩ := mem_Aof.1 ha
      have hpM : p ∈ M₂ := hPM hp
      refine mem_Aof.2 ⟨⟨p, hpM⟩ * b₁ * ⟨p, hpM⟩⁻¹ * b₁⁻¹, ?_, ?_⟩
      · have e1 : (((⟨p, hpM⟩ * b₁ * ⟨p, hpM⟩⁻¹ * b₁⁻¹ : ↥M₂)) : X) =
            p * (b₁ : X) * p⁻¹ * (b₁ : X)⁻¹ := rfl
        rw [e1]
        constructor
        · have h1 := c.P_norm (b₁ : X) (hPeT g hgP _ hb₁) p⁻¹ (P.inv_mem hp)
          have h2 := P.mul_mem hp h1
          simpa [mul_assoc] using h2
        · have h2 := hPeN g hgP p (hPD hp) _ hb₁
          exact (conjSubgroup P g).mul_mem h2 ((conjSubgroup P g).inv_mem hb₁)
      · simp only [map_mul, map_inv]
        rw [hπid ⟨p, hpM⟩ (hPW hp)]
        simp [commutatorElement_def]
    have hcardle : Nat.card ↥(P ⊓ Aof π (conjSubgroup P g)) ≤
        Nat.card ↥(P ⊓ conjSubgroup P g) :=
      (Subgroup.card_le_of_le hinc).trans (card_Aof_le π hPP1M)
    have hP1N : conjSubgroup P g ≤ normalizer (P : Set X) := fun b hb => hTP (hPeT g hgP b hb)
    have hcoeS₀ : ((P ⊔ conjSubgroup P g : Subgroup X) : Set X) =
        (P : Set X) * (conjSubgroup P g : Set X) :=
      Subgroup.coe_mul_of_right_le_normalizer_left P (conjSubgroup P g) hP1N
    have hS₀M : P ⊔ conjSubgroup P g ≤ M₂ := sup_le hPM hP1M
    have hS₀D : P ⊔ conjSubgroup P g ≤ D := sup_le hPD (fun b hb => hPeD g hgP b hb)
    have hS₀T : P ⊔ conjSubgroup P g ≤ T := hS₀D.trans hDT
    have hS₀card : Nat.card ↥(P ⊔ conjSubgroup P g) ≤ 2 * Nat.card ↥P := by
      have h1 := card_mul_inf P (conjSubgroup P g)
      have h2 : Nat.card ↥((P : Set X) * (conjSubgroup P g : Set X)) =
          Nat.card ↥(P ⊔ conjSubgroup P g) := by rw [← hcoeS₀]; rfl
      rw [h2, card_conjSubgroup P g] at h1
      have hp : 0 < Nat.card ↥P := Nat.card_pos
      have h3 : Nat.card ↥P ≤ 2 * Nat.card ↥(P ⊓ conjSubgroup P g) := by omega
      have h4 : Nat.card ↥(P ⊔ conjSubgroup P g) * Nat.card ↥P ≤ (2 * Nat.card ↥P) * Nat.card ↥P := by
        calc Nat.card ↥(P ⊔ conjSubgroup P g) * Nat.card ↥P
            ≤ Nat.card ↥(P ⊔ conjSubgroup P g) * (2 * Nat.card ↥(P ⊓ conjSubgroup P g)) :=
              Nat.mul_le_mul_left _ h3
          _ = 2 * (Nat.card ↥(P ⊔ conjSubgroup P g) * Nat.card ↥(P ⊓ conjSubgroup P g)) := by ring
          _ = (2 * Nat.card ↥P) * Nat.card ↥P := by rw [h1]; ring
      exact Nat.le_of_mul_le_mul_right h4 hp
    have hnotle : ¬ Aof π (conjSubgroup P g) ≤ P := fun h1 =>
      hA1P (Subgroup.eq_of_le_of_card_ge h1 (by rw [hA1card]))
    have hPA1W : P ⊔ Aof π (conjSubgroup P g) = W := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hPW hA1W) ?_
      have hlt : P < P ⊔ Aof π (conjSubgroup P g) := by
        refine lt_of_le_of_ne le_sup_left (fun h1 => hnotle ?_)
        have := (le_sup_right : Aof π (conjSubgroup P g) ≤ P ⊔ Aof π (conjSubgroup P g))
        rwa [← h1] at this
      have hdvd1 : Nat.card ↥P ∣ Nat.card ↥(P ⊔ Aof π (conjSubgroup P g)) :=
        Subgroup.card_dvd_of_le le_sup_left
      have hdvd2 : Nat.card ↥(P ⊔ Aof π (conjSubgroup P g)) ∣ Nat.card ↥W :=
        Subgroup.card_dvd_of_le (sup_le hPW hA1W)
      have hlt' := Subgroup.card_lt_of_lt hlt
      have hp : 0 < Nat.card ↥P := Nat.card_pos
      obtain ⟨m, hm⟩ := hdvd1
      rw [hm, hWcard] at hdvd2
      rw [hm] at hlt'
      have hmle : m ∣ 2 := (Nat.mul_dvd_mul_iff_left hp).1 hdvd2
      have hm2 : m ≤ 2 := Nat.le_of_dvd (by norm_num) hmle
      have hm1 : 1 < m := by
        by_contra hcon
        have : m ≤ 1 := by omega
        have := Nat.mul_le_mul_left (Nat.card ↥P) this
        omega
      have : m = 2 := by omega
      rw [hm, this, hWcard]
    have hWS₀ : W ≤ Aof π (P ⊔ conjSubgroup P g) := by
      have h1 : P ⊔ Aof π (conjSubgroup P g) ≤ Aof π (P ⊔ conjSubgroup P g) :=
        sup_le (calc P = Aof π P := hAP.symm
          _ ≤ Aof π (P ⊔ conjSubgroup P g) := Aof_mono le_sup_left) (Aof_mono le_sup_right)
      calc W = P ⊔ Aof π (conjSubgroup P g) := hPA1W.symm
        _ ≤ Aof π (P ⊔ conjSubgroup P g) := h1
    have hS₀eq : Nat.card ↥(P ⊔ conjSubgroup P g) = Nat.card ↥W := by
      apply le_antisymm
      · calc Nat.card ↥(P ⊔ conjSubgroup P g) ≤ 2 * Nat.card ↥P := hS₀card
          _ = Nat.card ↥W := by rw [hWcard]; ring
      · calc Nat.card ↥W ≤ Nat.card ↥(Aof π (P ⊔ conjSubgroup P g)) :=
              Subgroup.card_le_of_le hWS₀
          _ ≤ Nat.card ↥(P ⊔ conjSubgroup P g) := card_Aof_le π hS₀M
    have hS₀inj := inj_of_card_Aof π hS₀M
      (le_antisymm (card_Aof_le π hS₀M) (hS₀eq.le.trans (Subgroup.card_le_of_le hWS₀)))
    have hS1eq : conjSubgroup (P ⊔ conjSubgroup P g) g =
        conjSubgroup P g ⊔ conjSubgroup P (g * g) := by
      rw [conjSubgroup_sup, conjSubgroup_conjSubgroup]
    have hP2D : conjSubgroup P (g * g) ≤ D := fun b hb => hPeD (g * g) hggN b hb
    have hP2N1 : conjSubgroup P (g * g) ≤ normalizer (conjSubgroup P g : Set X) := by
      intro d hd
      refine mem_normalizer_of_conj_le (fun b hb => ?_)
      have := hPeN g hgP d⁻¹ (D.inv_mem (hP2D hd)) b hb
      simpa using this
    have hcoeS1 : ((conjSubgroup P g ⊔ conjSubgroup P (g * g) : Subgroup X) : Set X) =
        (conjSubgroup P g : Set X) * (conjSubgroup P (g * g) : Set X) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hP2N1
    have hS1M : conjSubgroup P g ⊔ conjSubgroup P (g * g) ≤ M₂ := sup_le hP1M hP2M
    have hS1T : conjSubgroup P g ⊔ conjSubgroup P (g * g) ≤ T :=
      sup_le (fun b hb => hPeT g hgP b hb) (fun b hb => hPeT (g * g) hggN b hb)
    have hAS1 : Aof π (conjSubgroup P g ⊔ conjSubgroup P (g * g)) ≤ Aof π (conjSubgroup P g) := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := mem_Aof.1 hy
      have hb' : (b : X) ∈ ((conjSubgroup P g ⊔ conjSubgroup P (g * g) : Subgroup X) : Set X) := hb
      rw [hcoeS1] at hb'
      obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ := hb'
      have hb₁M : b₁ ∈ M₂ := hP1M hb₁
      have hb₂M : b₂ ∈ M₂ := hP2M hb₂
      have hbeq : b = ⟨b₁, hb₁M⟩ * ⟨b₂, hb₂M⟩ := Subtype.ext hb12.symm
      rw [hbeq, map_mul]
      refine (Aof π (conjSubgroup P g)).mul_mem (mem_Aof.2 ⟨⟨b₁, hb₁M⟩, hb₁, rfl⟩) ?_
      rw [hA12]
      exact mem_Aof.2 ⟨⟨b₂, hb₂M⟩, hb₂, rfl⟩
    have hS1card : Nat.card ↥(conjSubgroup P g ⊔ conjSubgroup P (g * g)) = Nat.card ↥W := by
      rw [← hS1eq, card_conjSubgroup, hS₀eq]
    have hnotinj : ¬ (∀ y y' : ↥M₂, (y : X) ∈ conjSubgroup P g ⊔ conjSubgroup P (g * g) →
        (y' : X) ∈ conjSubgroup P g ⊔ conjSubgroup P (g * g) → π y = π y' → y = y') := by
      intro hinj
      have h1 := card_Aof_of_inj π hS1M hinj
      have h2 := Subgroup.card_le_of_le hAS1
      rw [hA1card] at h2
      rw [hS1card, hWcard] at h1
      have hp : 0 < Nat.card ↥P := Nat.card_pos
      omega
    push Not at hnotinj
    obtain ⟨y, y', hy, hy', hyy', hne⟩ := hnotinj
    have hsS1 : (y : X)⁻¹ * (y' : X) ∈ conjSubgroup P g ⊔ conjSubgroup P (g * g) :=
      (conjSubgroup P g ⊔ conjSubgroup P (g * g)).mul_mem
        ((conjSubgroup P g ⊔ conjSubgroup P (g * g)).inv_mem hy) hy'
    have hsQ : (y : X)⁻¹ * (y' : X) ∈ Q := by
      have h1 : π (y⁻¹ * y') = 1 := by rw [map_mul, map_inv, hyy']; simp
      exact (hπker _).1 h1
    have hs1 : (y : X)⁻¹ * (y' : X) ≠ 1 := fun h1 =>
      hne (inv_mul_eq_one.1 (Subtype.ext h1 : y⁻¹ * y' = 1))
    have hsS1' : (y : X)⁻¹ * (y' : X) ∈ conjSubgroup (P ⊔ conjSubgroup P g) g := by
      rw [hS1eq]; exact hsS1
    have hts : g * ((y : X)⁻¹ * (y' : X)) * g⁻¹ ∈ P ⊔ conjSubgroup P g :=
      mem_conjSubgroup_iff.1 hsS1'
    let N₀ : Subgroup X := (P ⊔ conjSubgroup P g) ⊓ conjSubgroup Q g⁻¹
    have hmemN₀ : ∀ w : X, w ∈ N₀ ↔ w ∈ P ⊔ conjSubgroup P g ∧ g⁻¹ * w * g ∈ Q := by
      intro w
      show w ∈ (P ⊔ conjSubgroup P g) ⊓ conjSubgroup Q g⁻¹ ↔ _
      rw [Subgroup.mem_inf, mem_conjSubgroup_iff]
      simp
    have htN : g * ((y : X)⁻¹ * (y' : X)) * g⁻¹ ∈ N₀ := by
      refine (hmemN₀ _).2 ⟨hts, ?_⟩
      have e1 : g⁻¹ * (g * ((y : X)⁻¹ * (y' : X)) * g⁻¹) * g = (y : X)⁻¹ * (y' : X) := by group
      rw [e1]; exact hsQ
    have htne : g * ((y : X)⁻¹ * (y' : X)) * g⁻¹ ≠ 1 := by
      intro h1
      apply hs1
      calc (y : X)⁻¹ * (y' : X) = g⁻¹ * (g * ((y : X)⁻¹ * (y' : X)) * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hN₀norm : ∀ w ∈ P ⊔ conjSubgroup P g, ∀ n ∈ N₀, w * n * w⁻¹ ∈ N₀ := by
      intro w hw n hn
      obtain ⟨hnS, hnQ⟩ := (hmemN₀ n).1 hn
      refine (hmemN₀ _).2 ⟨(P ⊔ conjSubgroup P g).mul_mem
        ((P ⊔ conjSubgroup P g).mul_mem hw hnS) ((P ⊔ conjSubgroup P g).inv_mem hw), ?_⟩
      have hwS1 : g⁻¹ * w * g ∈ conjSubgroup P g ⊔ conjSubgroup P (g * g) := by
        rw [← hS1eq, mem_conjSubgroup_iff]
        have e1 : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
        rw [e1]; exact hw
      have h1 := c.Q_norm _ (hS1T hwS1) _ hnQ
      have e2 : g⁻¹ * (w * n * w⁻¹) * g =
          (g⁻¹ * w * g) * (g⁻¹ * n * g) * (g⁻¹ * w * g)⁻¹ := by group
      rw [e2]; exact h1
    have hS₀p : IsPGroup 2 ↥(P ⊔ conjSubgroup P g) := c.T_pgroup.to_le hS₀T
    have hN₀ne : N₀ ≠ ⊥ := fun h1 => by
      have := htN
      rw [h1, Subgroup.mem_bot] at this
      exact htne this
    obtain ⟨c', hc'N, hc'1, hc'cent⟩ := exists_central_of_normal (W := P ⊔ conjSubgroup P g) hS₀p
      (N := N₀) inf_le_left hN₀norm hN₀ne
    obtain ⟨hc'S, hc'Q⟩ := (hmemN₀ c').1 hc'N
    have hc'M : c' ∈ M₂ := hS₀M hc'S
    have hπc'cent : ∀ w ∈ W, w * π ⟨c', hc'M⟩ = π ⟨c', hc'M⟩ * w := by
      intro w hw
      obtain ⟨b, hb, rfl⟩ := mem_Aof.1 (hWS₀ hw)
      have h1 : (b : X) * c' = c' * (b : X) := hc'cent (b : X) hb
      have h1' : b * (⟨c', hc'M⟩ : ↥M₂) = ⟨c', hc'M⟩ * b := Subtype.ext h1
      calc π b * π ⟨c', hc'M⟩ = π (b * ⟨c', hc'M⟩) := (map_mul π b _).symm
        _ = π (⟨c', hc'M⟩ * b) := by rw [h1']
        _ = π ⟨c', hc'M⟩ * π b := map_mul π _ b
    have hzW : z ∈ W := hPW c.z_mem
    obtain ⟨-, -, -, hDW2⟩ := hD X W hWdih
    obtain ⟨hZW, -⟩ := hDW2 z hzW c.z_order (fun a ha => c.z_cent_T a (hWT ha))
    rcases hZW _ (hπW ⟨c', hc'M⟩) hπc'cent with h1 | h1
    · apply hc'1
      have := hS₀inj ⟨c', hc'M⟩ 1 hc'S (P ⊔ conjSubgroup P g).one_mem (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · have hzS : z ∈ P ⊔ conjSubgroup P g := (le_sup_left : P ≤ P ⊔ conjSubgroup P g) c.z_mem
      have hzM : z ∈ M₂ := hPM c.z_mem
      have hcz : c' = z := by
        have := hS₀inj ⟨c', hc'M⟩ ⟨z, hzM⟩ hc'S hzS (by rw [h1, hπid ⟨z, hzM⟩ hzW])
        exact congrArg Subtype.val this
      rw [hcz, hzfix g hgP] at hc'Q
      have : z ∈ P ⊓ Q := ⟨c.z_mem, hc'Q⟩
      rw [c.PQ_inf, Subgroup.mem_bot] at this
      exact c.z_ne_one this

end CFSG.GH74.GLS.C3.Layer1.P34
