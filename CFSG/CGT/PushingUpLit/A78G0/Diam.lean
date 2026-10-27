module

public import CFSG.CGT.PushingUpLit.A78G0.GQ
public import CFSG.CGT.PushingUpLit.A78G0.KCount
public import CFSG.CGT.PushingUpLit.A78G0.Conn
public import CFSG.CGT.PushingUpLit.A78G0.DualData
import CFSG.CGT.PushingUpLit.A78G0.Fibers

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4

section Packing

variable {G : Type} [Group G] [Finite G] {Z : Subgroup G} {e : ℕ} {A : Subgroup G}

theorem SigmaCliques.ncard_le_of_pairwise (hA : SigmaCliques Z e A) {I : Set (Subgroup G)}
    (hIS : I ⊆ sigmaSet (zClass Z) A) (hI : ∀ X ∈ I, ∀ X' ∈ I, Commuting X X' → X = X') :
    I.ncard ≤ 2 ^ e + 1 := by
  let cl : Subgroup G → Set (Subgroup G) :=
    fun X => {Y | Y ∈ sigmaSet (zClass Z) A ∧ Commuting X Y}
  have hcl : ∀ X ∈ I, (cl X).ncard = 2 ^ e := fun X hX =>
    (Nat.card_coe_set_eq (cl X)).symm.trans (hA.clique X (hIS hX))
  have hP := ncard_pairs I cl (2 ^ e) hcl
  have hle : {p : Subgroup G × Subgroup G | p.1 ∈ I ∧ p.2 ∈ cl p.1}.ncard ≤
      (sigmaSet (zClass Z) A).ncard := by
    refine Set.ncard_le_ncard_of_injOn Prod.snd (fun p hp => hp.2.1) ?_
    rintro ⟨X, Y⟩ ⟨hXI, hXY⟩ ⟨X', Y'⟩ ⟨hX'I, hX'Y⟩ hYY
    have hYY' : Y = Y' := hYY
    subst hYY'
    have hXX' : X = X' := hI X hXI X' hX'I
      (hA.trans X (hIS hXI) Y hXY.1 X' (hIS hX'I) hXY.2 (commuting_symm hX'Y.2))
    rw [hXX']
  have hS : (sigmaSet (zClass Z) A).ncard = 2 ^ e * (2 ^ e + 1) :=
    (Nat.card_coe_set_eq (sigmaSet (zClass Z) A)).symm.trans hA.card
  rw [hP, hS] at hle
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.two_pow_pos e)
  calc I.ncard * 2 ^ e ≤ 2 ^ e * (2 ^ e + 1) := hle
    _ = (2 ^ e + 1) * 2 ^ e := Nat.mul_comm _ _

theorem SigmaCliques.exists_commuting (hA : SigmaCliques Z e A) {Q : Set (Subgroup G)}
    (hQS : Q ⊆ sigmaSet (zClass Z) A) (hQ : ∀ X ∈ Q, ∀ X' ∈ Q, Commuting X X' → X = X')
    (hQc : Q.ncard = 2 ^ e + 1) {Y : Subgroup G} (hY : Y ∈ sigmaSet (zClass Z) A)
    (hYY : Commuting Y Y) : ∃ X ∈ Q, Commuting Y X := by
  by_contra hcon
  push Not at hcon
  have hYQ : Y ∉ Q := fun hy => hcon Y hy hYY
  have hins := hA.ncard_le_of_pairwise (I := insert Y Q) ?_ ?_
  · rw [Set.ncard_insert_of_notMem hYQ, hQc] at hins
    omega
  · intro X hX
    rcases hX with rfl | hX
    · exact hY
    · exact hQS hX
  · intro X hX X' hX' hc
    rcases hX with rfl | hX <;> rcases hX' with rfl | hX'
    · rfl
    · exact absurd hc (hcon X' hX')
    · exact absurd (commuting_symm hc) (hcon X hX)
    · exact hQ X hX X' hX' hc

end Packing

section Dual

variable {G : Type} [Group G] {Z : Subgroup G} {e : ℕ} {K₁ K₂ : Subgroup G}

structure SL2Dual (Z : Subgroup G) (e : ℕ) (K₁ K₂ : Subgroup G) : Prop where
  iso₁ : Nonempty (↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e))
  iso₂ : Nonempty (↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e))
  comm : Commuting K₁ K₂
  syl₁ : ∀ P : Subgroup G, P ≤ K₁ → Nat.card P = 2 ^ e → P ∈ zClass Z
  syl₂ : ∀ P : Subgroup G, P ≤ K₂ → Nat.card P = 2 ^ e → P ∈ zClass Z

theorem SL2Dual.symm (D : SL2Dual Z e K₁ K₂) : SL2Dual Z e K₂ K₁ :=
  ⟨D.iso₂, D.iso₁, commuting_symm D.comm, D.syl₂, D.syl₁⟩

theorem syl_zClass_cs {K : Subgroup G}
    (hsyl : ∀ P : Subgroup G, P ≤ K → Nat.card P = 2 ^ e → P ∈ zClass Z) (n : G)
    {P : Subgroup G} (hP : P ≤ cs K n) (hc : Nat.card P = 2 ^ e) : P ∈ zClass Z := by
  have h1 : cs P n⁻¹ ≤ K := by
    have := (cs_le_cs_iff n⁻¹).2 hP
    rwa [cs_cs_inv] at this
  have h2 : cs P n⁻¹ ∈ zClass Z := hsyl _ h1 (by rw [card_cs, hc])
  have h3 := (zClass_cs_iff (Z := Z) n).2 h2
  rwa [cs_inv_cs] at h3

theorem SL2Dual.conj (D : SL2Dual Z e K₁ K₂) (n : G) : SL2Dual Z e (cs K₁ n) (cs K₂ n) where
  iso₁ := D.iso₁.map fun φ => (csIso K₁ n).symm.trans φ
  iso₂ := D.iso₂.map fun φ => (csIso K₂ n).symm.trans φ
  comm := (commuting_cs_iff n).2 D.comm
  syl₁ _ hP hc := syl_zClass_cs D.syl₁ n hP hc
  syl₂ _ hP hc := syl_zClass_cs D.syl₂ n hP hc

variable [Finite G]

theorem SL2Dual.commonNbrs_eq (D : SL2Dual Z e K₁ K₂) (hZ : SigmaCliques Z e Z) (he : 2 ≤ e)
    {P P' : Subgroup G} (hP : P ≤ K₁) (hP' : P' ≤ K₁) (hPc : Nat.card P = 2 ^ e)
    (hP'c : Nat.card P' = 2 ^ e) (hne : P ≠ P') :
    {X : Subgroup G | X ∈ zClass Z ∧ Commuting X P ∧ Commuting X P'} =
      {X : Subgroup G | X ≤ K₂ ∧ Nat.card X = 2 ^ e} := by
  obtain ⟨φ₁⟩ := D.iso₁
  obtain ⟨φ₂⟩ := D.iso₂
  have hsub : {X : Subgroup G | X ≤ K₂ ∧ Nat.card X = 2 ^ e} ⊆
      {X : Subgroup G | X ∈ zClass Z ∧ Commuting X P ∧ Commuting X P'} := by
    rintro X ⟨hX, hXc⟩
    exact ⟨D.syl₂ X hX hXc, fun x hx p hp => (D.comm p (hP hp) x (hX hx)).symm,
      fun x hx p hp => (D.comm p (hP' hp) x (hX hx)).symm⟩
  have hle : {X : Subgroup G | X ∈ zClass Z ∧ Commuting X P ∧ Commuting X P'}.ncard ≤
      {X : Subgroup G | X ≤ K₂ ∧ Nat.card X = 2 ^ e}.ncard := by
    rw [ncard_sylow_sl2 he φ₂]
    exact (Nat.card_coe_set_eq _).symm.trans_le
      (SigmaCliques.card_common_le hZ (D.syl₁ P hP hPc) (D.syl₁ P' hP' hP'c)
        (sylow_not_commuting φ₁ he hP hP' hPc hP'c hne))
  exact (Set.eq_of_subset_of_ncard_le hsub hle).symm

end Dual

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem sigmaCliques : SigmaCliques Z e Z := ⟨h.sigma_trans, h.sigma_clique, h.sigma_card⟩

theorem sigmaCliques_of_mem {A : Subgroup G} (hA : A ∈ zClass Z) : SigmaCliques Z e A := by
  obtain ⟨g, rfl⟩ := hA
  exact h.sigmaCliques.conj g

theorem commuting_self {B : Subgroup G} (hB : B ∈ zClass Z) : Commuting B B :=
  fun x hx y hy => ((h.elemAb2_of_mem_zClass hB) x hx y hy).1

theorem card_of_mem_zClass {B : Subgroup G} (hB : B ∈ zClass Z) : Nat.card B = 2 ^ e := by
  obtain ⟨g, rfl⟩ := hB
  exact (card_cs Z g).trans h.card_Z

end G0Core

section KCountAt

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  {h : G0Core G L₁ L₂ V W Z Z₂ e} {K A : Subgroup G}

theorem kcount_cs (hK : KData h K A) (m : G) {B C : Subgroup G}
    (hB : B ∈ sigmaSet (zClass Z) (cs Z m)) (hC : C ∈ sigmaSet (zClass Z) (cs Z m))
    (hBC : ¬ Commuting B C) : ∃ l ∈ L₁, B ⊔ C = cs K (m * l) := by
  have hB' := (mem_sigmaSet_cs_iff m).1 hB
  have hC' := (mem_sigmaSet_cs_iff m).1 hC
  obtain ⟨l, hl, hKl⟩ := kcount hK hB' hC' fun hc => hBC ((commuting_cs_iff m⁻¹).1 hc)
  refine ⟨l, hl, ?_⟩
  have : B ⊔ C = cs (cs B m⁻¹ ⊔ cs C m⁻¹) m := by
    rw [cs_sup, cs_inv_cs, cs_inv_cs]
  rw [this, hKl, ← cs_mul]

theorem DualBase.exists_sl2Dual (hd : DualBase h) :
    ∃ K A I : Subgroup G, KData h K A ∧ SL2Dual Z e K I := by
  obtain ⟨K, A, I, hK, hI, hKI, hΔ⟩ := hd
  refine ⟨K, A, I, hK, ⟨kData_iso hK, hI, hKI, fun P hP hc => ?_, hΔ⟩⟩
  exact (kData_sylow_mem hK L₁.one_mem (by rwa [cs_one]) hc).1

end KCountAt

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem diam_step (hd : DualBase h) {X₀ X₁ X₂ X₃ : Subgroup G} (h0 : X₀ ∈ zClass Z)
    (h1 : X₁ ∈ zClass Z) (h2 : X₂ ∈ zClass Z) (h3 : X₃ ∈ zClass Z) (h01 : Commuting X₀ X₁)
    (h12 : Commuting X₁ X₂) (h23 : Commuting X₂ X₃) :
    ∃ U ∈ zClass Z, Commuting X₀ U ∧ Commuting U X₃ := by
  by_cases h13 : Commuting X₁ X₃
  · exact ⟨X₁, h1, h01, h13⟩
  by_cases hX01 : X₀ = X₁
  · subst hX01
    exact ⟨X₂, h2, h12, h23⟩
  have hne12 : X₁ ≠ X₂ := by
    rintro rfl
    exact h13 h23
  have hne32 : X₃ ≠ X₂ := by
    rintro rfl
    exact h13 h12
  obtain ⟨K, A, I, hK, D⟩ := hd.exists_sl2Dual
  obtain ⟨m, rfl⟩ := h2
  obtain ⟨l, hl, hK'⟩ := kcount_cs hK m ⟨h1, hne12, commuting_symm h12⟩ ⟨h3, hne32, h23⟩ h13
  have D' := D.conj (m * l)
  rw [← hK'] at D'
  obtain ⟨φ₂⟩ := D'.iso₂
  have hQc : {P : Subgroup G | P ≤ cs I (m * l) ∧ Nat.card P = 2 ^ e}.ncard = 2 ^ e + 1 :=
    ncard_sylow_sl2 h.two_le φ₂
  have hX1 := h.sigmaCliques_of_mem h1
  have hQS : {P : Subgroup G | P ≤ cs I (m * l) ∧ Nat.card P = 2 ^ e} ⊆
      sigmaSet (zClass Z) X₁ := by
    rintro P ⟨hP, hPc⟩
    refine ⟨D'.syl₂ P hP hPc, ?_, fun a ha p hp => D'.comm a (Subgroup.mem_sup_left ha) p (hP hp)⟩
    rintro rfl
    exact h13 fun a ha b hb => (D'.comm b (Subgroup.mem_sup_right hb) a (hP ha)).symm
  have hQpair : ∀ P ∈ {P : Subgroup G | P ≤ cs I (m * l) ∧ Nat.card P = 2 ^ e},
      ∀ P' ∈ {P : Subgroup G | P ≤ cs I (m * l) ∧ Nat.card P = 2 ^ e},
      Commuting P P' → P = P' := by
    intro P hP P' hP' hc
    by_contra hne
    exact sylow_not_commuting φ₂ h.two_le hP.1 hP'.1 hP.2 hP'.2 hne hc
  obtain ⟨P, hPQ, hX0P⟩ := hX1.exists_commuting hQS hQpair hQc
    ⟨h0, hX01, commuting_symm h01⟩ (h.commuting_self h0)
  exact ⟨P, D'.syl₂ P hPQ.1 hPQ.2, hX0P,
    fun p hp b hb => (D'.comm b (Subgroup.mem_sup_right hb) p (hPQ.1 hp)).symm⟩

theorem diam2 (hd : DualBase h) :
    ∀ B ∈ zClass Z, ∀ C ∈ zClass Z, ∃ U ∈ zClass Z, Commuting B U ∧ Commuting U C := by
  intro B hB C hC
  have hconn := h.connected B hB C hC
  induction hconn with
  | refl => exact ⟨B, hB, h.commuting_self hB, h.commuting_self hB⟩
  | tail _ hYC ih =>
    obtain ⟨U, hU, hBU, hUY⟩ := ih hYC.1
    exact h.diam_step hd hB hU hYC.1 hYC.2.1 hBU hUY hYC.2.2

end G0Core

end CFSG.CGT.PushingUpLit.A78G0
