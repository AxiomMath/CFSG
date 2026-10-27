module

public import Certificates.Data.Kernel.S63K.ConjTree
public import CFSG.Certificates.Kernel.S63K.EnumSound
public import CFSG.LargeExtraspecial.S63CD4Kit

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.S63K

open CFSG.KC.Co1F2 CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native CFSG.KS.SporSch.M24
open CFSG.KC.Enum CFSG.KS

theorem rec_true {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem shiftLeft_576 : Nat.shiftLeft 1 576 = 2 ^ 576 := Nat.one_shiftLeft 576

theorem idM_eq : idM = idP := by decide +kernel

theorem wordK_cons (G : ℕ → ℕ) (I k : ℕ) (w : List ℕ) :
    wordK G I (k :: w) = CFSG.KC.F2W.mulW 24 (G k) (wordK G I w) := rfl

theorem wordR_eq {gs : Array (Array ℕ)} {G : ℕ → ℕ} :
    ∀ {w : List ℕ}, (∀ k ∈ w, gs[k]! = unpackR 24 (G k)) → wordR gs w = unpackR 24 (wordK G idM w)
  | [], _ => by
    change oneR = unpackR 24 idM
    rw [idM_eq, oneR_eq]
  | k :: w, h => by
    have ih := wordR_eq (w := w) fun k' hk' => h k' (List.mem_cons_of_mem k hk')
    rw [wordK_cons, ← mulR_unpackR, ← ih, ← h k List.mem_cons_self]
    rfl

theorem conjR_unpackR (G : ℕ → ℕ) (X l : ℕ) :
    conjR (unpackR 24 (G l)) (unpackR 24 X) = unpackR 24 (cjStepK G X l) := by
  rw [conjR, mulR_unpackR, mulR_unpackR]
  rfl

variable {P Q S : ℕ → ℕ} {F : ℕ → ℕ → ℕ} {ng N : ℕ}

theorem treeAtK_spec {i : ℕ} (h : treeAtK F P Q ng i = true) (hi : 0 < i) :
    Q i / ng < i ∧ P i = F (P (Q i / ng)) (Q i % ng) := by
  unfold treeAtK at h
  rcases rec_true h with ⟨h0, -⟩ | ⟨-, h1⟩
  · exact absurd (Nat.eq_of_beq_eq_true h0) (Nat.pos_iff_ne_zero.1 hi)
  · simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true] at h1
    exact ⟨Nat.le_of_ble_eq_true h1.1, Nat.eq_of_beq_eq_true h1.2⟩

variable {H : Type*} [Group H] {E : H →* Matrix (Fin 24) (Fin 24) (ZMod 2)}

theorem repE_cjStepK {G : ℕ → ℕ} {gH : ℕ → H} {X l : ℕ} {x : H}
    (hG : RepE E (unpackR 24 (G l)) (gH l)) (hg : gH l * gH l = 1) (hX : RepE E (unpackR 24 X) x) :
    RepE E (unpackR 24 (cjStepK G X l)) (gH l * x * (gH l)⁻¹) := by
  have := repE_conjR hG hX hg
  rwa [conjR_unpackR] at this

theorem exists_conj_of_treeAtK {G : ℕ → ℕ} {gH : ℕ → H} (hng : 0 < ng)
    (hG : ∀ l < ng, RepE E (unpackR 24 (G l)) (gH l) ∧ gH l * gH l = 1)
    (ht : ∀ i < N, treeAtK (cjStepK G) P Q ng i = true) {x₀ : H}
    (hx : RepE E (unpackR 24 (P 0)) x₀) :
    ∀ i < N, ∃ c : H, RepE E (unpackR 24 (P i)) (c * x₀ * c⁻¹) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨1, by simpa using hx⟩
    · obtain ⟨hp, he⟩ := treeAtK_spec (ht i hi) hi0
      obtain ⟨c, hc⟩ := ih _ hp (hp.trans hi)
      have hl : Q i % ng < ng := Nat.mod_lt _ hng
      refine ⟨gH (Q i % ng) * c, ?_⟩
      rw [he]
      have := repE_cjStepK (hG _ hl).1 (hG _ hl).2 hc
      have e : gH (Q i % ng) * (c * x₀ * c⁻¹) * (gH (Q i % ng))⁻¹ =
          gH (Q i % ng) * c * x₀ * (gH (Q i % ng) * c)⁻¹ := by
        group
      rwa [e] at this

theorem mod_eq_of_repE {A B : ℕ} {a : H} (hA : RepE E (unpackR 24 A) a)
    (hB : RepE E (unpackR 24 B) a) : A % 2 ^ 576 = B % 2 ^ 576 :=
  unpackR_inj.1 (arr_eq_of_repE (validR_unpackR A) (validR_unpackR B) hA hB)

theorem card_centralizer_mul_le_of_treeAtK [Finite H] {G : ℕ → ℕ} {gH : ℕ → H} (hng : 0 < ng)
    (hG : ∀ l < ng, RepE E (unpackR 24 (G l)) (gH l) ∧ gH l * gH l = 1)
    (ht : ∀ i < N, treeAtK (cjStepK G) P Q ng i = true) (hd : bfsDistK P S N = true) {x₀ : H}
    (hx : RepE E (unpackR 24 (P 0)) x₀) :
    Nat.card (Subgroup.centralizer ({x₀} : Set H)) * N ≤ Nat.card H := by
  classical
  obtain ⟨hlt, hinj⟩ := bfsDistK_sound hd
  choose! c hc using exists_conj_of_treeAtK hng hG ht hx
  have hle : N ≤ (conjugatesOf x₀).ncard := by
    let f : Fin N → H := fun i => c i * x₀ * (c i)⁻¹
    have hf : Function.Injective f := by
      intro i j hij
      have hij' : c i * x₀ * (c i)⁻¹ = c j * x₀ * (c j)⁻¹ := hij
      have hj : RepE E (unpackR 24 (P j)) (c i * x₀ * (c i)⁻¹) := by
        rw [hij']
        exact hc j j.2
      have h1 := mod_eq_of_repE (hc i i.2) hj
      rw [Nat.mod_eq_of_lt (hlt i i.2), Nat.mod_eq_of_lt (hlt j j.2)] at h1
      exact Fin.ext (hinj i i.2 j j.2 h1)
    have hsub : Set.range f ⊆ conjugatesOf x₀ := by
      rintro _ ⟨i, rfl⟩
      exact isConj_iff.2 ⟨c i, rfl⟩
    calc N = Nat.card (Fin N) := (Nat.card_fin _).symm
      _ = (Set.range f).ncard := by
          rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hf]
      _ ≤ (conjugatesOf x₀).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hidx := Subgroup.card_mul_index (Subgroup.centralizer ({x₀} : Set H))
  rw [Subgroup.index_centralizer_eq_ncard] at hidx
  calc Nat.card (Subgroup.centralizer ({x₀} : Set H)) * N ≤
        Nat.card (Subgroup.centralizer ({x₀} : Set H)) * (conjugatesOf x₀).ncard :=
        Nat.mul_le_mul_left _ hle
    _ = Nat.card H := hidx

theorem tagAtK_spec {I : ℕ} {A B : ℕ → ℕ} {NA NB x t : ℕ} (h : tagAtK I A NA B NB x t = true)
    (hsq : CFSG.KC.F2W.mulW 24 x x % 2 ^ 576 = I) (hne : x ≠ I) :
    (∃ j < NA, A j = x) ∨ ∃ j < NB, B j = x := by
  unfold tagAtK at h
  have hb : Nat.beq (Nat.mod (CFSG.KC.F2W.mulW 24 x x) (Nat.shiftLeft 1 576)) I = true := by
    rw [shiftLeft_576, Nat.beq_eq]
    exact hsq
  rcases rec_true h with ⟨-, h1⟩ | ⟨h0, h1⟩
  · rcases rec_true h1 with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact absurd (Nat.eq_of_beq_eq_true h2) hne
    · exact absurd (h2.symm.trans hb) Bool.false_ne_true
  · have ht : t ≠ 0 := Nat.ne_of_beq_eq_false h0
    rcases rec_true h1 with ⟨h2, h3⟩ | ⟨-, h3⟩
    · have := Nat.le_of_ble_eq_true h2
      exact Or.inl ⟨t - 1, by omega, Nat.eq_of_beq_eq_true h3⟩
    · rw [MatL.bAnd_eq, Bool.and_eq_true] at h3
      exact Or.inr ⟨t - 1 - NA, Nat.le_of_ble_eq_true h3.1, Nat.eq_of_beq_eq_true h3.2⟩

variable {G PAR LAB W : ℕ → ℕ}

theorem row_clos (h : ℕ) : ∀ k l c, bfsRowK (stepK G) P PAR LAB W ng h k l c ≠ 0 →
    ∀ j, l ≤ j → j < l + k → W (h * ng + j) < bfsRowK (stepK G) P PAR LAB W ng h k l c ∧
      P (W (h * ng + j)) = stepK G (P h) j := by
  intro k
  induction k with
  | zero => intro l c _ j h1 h2; omega
  | succ k ih =>
    intro l c hne j h1 h2
    rw [bfsRowK_succ] at hne ⊢
    split at hne
    · rename_i hw
      rw [if_pos hw]
      split at hne
      · rename_i hp
        rw [if_pos hp]
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact ⟨Nat.lt_of_lt_of_le hw (bfsRowK_mono h _ _ _ hne), hp⟩
        · exact ih _ _ hne j (by omega) (by omega)
      · exact absurd rfl hne
    · rename_i hw
      rw [if_neg hw]
      split at hne
      · rename_i hp
        rw [if_pos hp]
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · rw [hp.1]
          exact ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self c) (bfsRowK_mono h _ _ _ hne), hp.2.1⟩
        · exact ih _ _ hne j (by omega) (by omega)
      · exact absurd rfl hne

theorem run_clos (cap : ℕ) : ∀ fuel h c, bfsRunK (stepK G) P PAR LAB W ng cap fuel h c ≠ 0 →
    bfsRunK (stepK G) P PAR LAB W ng cap fuel h c < cap →
    ∀ h', h ≤ h' → h' < bfsRunK (stepK G) P PAR LAB W ng cap fuel h c → ∀ l < ng,
      W (h' * ng + l) < bfsRunK (stepK G) P PAR LAB W ng cap fuel h c ∧
        P (W (h' * ng + l)) = stepK G (P h') l := by
  intro fuel
  induction fuel with
  | zero => intro h c hne; exact absurd rfl hne
  | succ fuel ih =>
    intro h c hne hcap h' hh' hlt l hl
    rw [bfsRunK_succ] at hne hcap hlt ⊢
    split at hne
    · rename_i hc
      rw [if_pos hc] at hcap hlt ⊢
      split at hne
      · exact absurd rfl hne
      · rename_i hr
        rw [if_neg hr] at hcap hlt ⊢
        rcases Nat.eq_or_lt_of_le hh' with rfl | hh'
        · obtain ⟨h1, h2⟩ := row_clos _ ng 0 c hr l (Nat.zero_le _) (by omega)
          exact ⟨Nat.lt_of_lt_of_le h1 (bfsRunK_mono cap fuel _ _ hne), h2⟩
        · exact ih _ _ hne hcap h' hh' hlt l hl
    · rename_i hc
      rw [if_neg hc] at hcap hlt
      exact absurd ⟨by omega, hcap⟩ hc

theorem closOK_of_bfsK {R : ℕ} (h : bfsK (stepK G) P PAR LAB W S ng (N + 1) N R = true) :
    closOK G P W ng N = true := by
  obtain ⟨hN, -, -, -, -, hr⟩ := bfsK_sound h
  have hc := run_clos (G := G) (P := P) (PAR := PAR) (LAB := LAB) (W := W) (ng := ng) (N + 1)
    (N + 1) 0 1 (by rw [hr]; omega) (by rw [hr]; omega)
  rw [hr] at hc
  unfold closOK
  refine MatL.allN_iff.2 fun h hh => MatL.allN_iff.2 fun l hl => ?_
  obtain ⟨h1, h2⟩ := hc h (Nat.zero_le _) hh l hl
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  exact ⟨h1, h2⟩

end CFSG.KC.S63K

end
