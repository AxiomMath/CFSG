module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2G

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 Certificates.FzBU

private theorem fzb_beta_split {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P)
    (q s lam : G) {w u : ℕ} (hu : u < 64) :
    fzbBeta C q s lam (64 * w + u) = C.dec u * fzbAlpha q s lam w := by
  unfold fzbBeta
  have hmod : (64 * w + u) % 64 = u := by omega
  have hdiv : (64 * w + u) / 64 = w := by omega
  rw [hmod, hdiv]

private theorem fzb_beta_lt64 {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P)
    (q s lam : G) {x : ℕ} (hx : x < 64) : fzbBeta C q s lam x = C.dec x := by
  unfold fzbBeta
  rw [Nat.mod_eq_of_lt hx, Nat.div_eq_of_lt hx, fzb_alpha_zero, mul_one]

private theorem fzb_alpha_mem {G : Type} [Group G] {T : Subgroup G} {q s lam : G}
    (hq : q ∈ T) (hs : s ∈ T) (hy : lam ∈ T) (w : ℕ) : fzbAlpha q s lam w ∈ T := by
  unfold fzbAlpha
  exact T.mul_mem (T.mul_mem (T.pow_mem hq _) (T.pow_mem hs _)) (T.pow_mem hy _)

private theorem fzb_alpha_pow {G : Type} [Group G] {P : Subgroup G} {C : FzbCoding P}
    {c : Bool} {q s lam : G} (hE : FzbExact C c q s lam) {w : ℕ} (hw : w < 16) (n : ℕ) :
    ∃ w' < 16, fzbAlpha q s lam w' = (fzbAlpha q s lam w) ^ n := by
  induction n with
  | zero => exact ⟨0, by norm_num, by rw [fzb_alpha_zero, pow_zero]⟩
  | succ n ih =>
    obtain ⟨w', hw', he⟩ := ih
    refine ⟨amul w' w, fzb_amul_lt _ _, ?_⟩
    rw [pow_succ, ← he, fzb_alpha_mul hE.q_pow hE.s_sq hE.y_sq hE.s_q hE.y_q hE.y_s hw' hw]

private theorem fzb_alpha_inv {G : Type} [Group G] [Finite G] {P : Subgroup G}
    {C : FzbCoding P} {c : Bool} {q s lam : G} (hE : FzbExact C c q s lam)
    {w : ℕ} (hw : w < 16) :
    ∃ w' < 16, fzbAlpha q s lam w' = (fzbAlpha q s lam w)⁻¹ := by
  obtain ⟨w', hw', he⟩ := fzb_alpha_pow hE hw (orderOf (fzbAlpha q s lam w) - 1)
  refine ⟨w', hw', ?_⟩
  have h1 : 1 ≤ orderOf (fzbAlpha q s lam w) := orderOf_pos _
  have hmul : fzbAlpha q s lam w * fzbAlpha q s lam w ^
      (orderOf (fzbAlpha q s lam w) - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel h1, pow_orderOf_eq_one]
  have hinv : (fzbAlpha q s lam w)⁻¹ =
      fzbAlpha q s lam w ^ (orderOf (fzbAlpha q s lam w) - 1) :=
    inv_eq_of_mul_eq_one_right hmul
  rw [he, ← hinv]

private theorem fzb_alpha_conj_mem {G : Type} [Group G] {P : Subgroup G}
    {C : FzbCoding P} {c : Bool} {q s lam : G} (hE : FzbExact C c q s lam)
    {w : ℕ} (hw : w < 16) {p : G} (hp : p ∈ P) :
    fzbAlpha q s lam w * p * (fzbAlpha q s lam w)⁻¹ ∈ P := by
  obtain ⟨u, hu, rfl⟩ := C.exists_dec hp
  obtain ⟨heq, hlt⟩ := fzb_alpha_act hE hw hu
  rw [heq]
  exact C.dec_mem _ hlt

private theorem fzb_T2_repr {G : Type} [Group G] [Finite G] {P T₂ : Subgroup G}
    {C : FzbCoding P} {c : Bool} {q s lam : G} (hE : FzbExact C c q s lam)
    (hP : P ≤ T₂) (hqT : q ∈ T₂) (hsT : s ∈ T₂) (hyT : lam ∈ T₂)
    (hgen : T₂ = P ⊔ closure {q, s, lam}) :
    ∀ g ∈ T₂, ∃ p ∈ P, ∃ w < 16, g = p * fzbAlpha q s lam w := by
  intro g hg
  have hg' : g ∈ Subgroup.closure ((P : Set G) ∪ {q, s, lam}) := by
    have hsup : P ⊔ Subgroup.closure ({q, s, lam} : Set G) =
        Subgroup.closure ((P : Set G) ∪ {q, s, lam}) := by
      simp only [Subgroup.closure_union, Subgroup.closure_eq]
    rw [hgen] at hg
    rwa [hsup] at hg
  clear hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxP | hxq | hxs | hxl
    · exact ⟨x, hxP, 0, by norm_num, by rw [fzb_alpha_zero, mul_one]⟩
    · refine ⟨1, P.one_mem, 1, by norm_num, ?_⟩
      rw [hxq, (fzb_alpha_gens q s lam).1, one_mul]
    · refine ⟨1, P.one_mem, 4, by norm_num, ?_⟩
      rw [hxs, (fzb_alpha_gens q s lam).2.1, one_mul]
    · refine ⟨1, P.one_mem, 8, by norm_num, ?_⟩
      rw [hxl, (fzb_alpha_gens q s lam).2.2.1, one_mul]
  | one => exact ⟨1, P.one_mem, 0, by norm_num, by rw [fzb_alpha_zero, mul_one]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨p, hp, w, hw, rfl⟩ := ihx
    obtain ⟨p', hp', w', hw', rfl⟩ := ihy
    refine ⟨p * (fzbAlpha q s lam w * p' * (fzbAlpha q s lam w)⁻¹),
      P.mul_mem hp (fzb_alpha_conj_mem hE hw hp'), amul w w', fzb_amul_lt _ _, ?_⟩
    rw [← fzb_alpha_mul hE.q_pow hE.s_sq hE.y_sq hE.s_q hE.y_q hE.y_s hw hw']
    group
  | inv x hx ih =>
    obtain ⟨p, hp, w, hw, rfl⟩ := ih
    obtain ⟨w', hw', hw'_eq⟩ := fzb_alpha_inv hE hw
    refine ⟨fzbAlpha q s lam w' * p⁻¹ * (fzbAlpha q s lam w')⁻¹,
      fzb_alpha_conj_mem hE hw' (P.inv_mem hp), w', hw', ?_⟩
    rw [hw'_eq]
    group

theorem fzb_chart_exact {G : Type} [Group G] [Finite G] {c : Bool} {T₂ P : Subgroup G}
    (C : FzbCoding P) {x₁ x₂ t q s lam : G} (hE : FzbExact C c q s lam) (hq2 : q ^ 2 = t)
    (hP : P ≤ T₂) (hqT : q ∈ T₂) (hsT : s ∈ T₂) (hyT : lam ∈ T₂)
    (hgen : T₂ = P ⊔ closure {q, s, lam}) (hcard : Nat.card T₂ = 2 ^ 10)
    (hZP : fourGrp x₁ x₂ ≤ P) (hZ : ∀ p ∈ P, p ∈ fourGrp x₁ x₂ ↔ C.enc p < 4) :
    FzbChart c T₂ P x₁ x₂ t q s lam (fzbBeta C q s lam) := by
  classical
  let β : ℕ → G := fzbBeta C q s lam
  have hmem : ∀ x < 1024, β x ∈ T₂ := by
    intro x hx
    have hu : x % 64 < 64 := Nat.mod_lt _ (by norm_num)
    have hw : x / 64 < 16 := by omega
    change C.dec (x % 64) * fzbAlpha q s lam (x / 64) ∈ T₂
    exact T₂.mul_mem (hP (C.dec_mem _ hu)) (fzb_alpha_mem hqT hsT hyT _)
  have hP_eq : ∀ g, g ∈ P ↔ ∃ x < 64, β x = g := by
    intro g
    constructor
    · intro hg
      refine ⟨C.enc g, C.enc_lt g hg, ?_⟩
      exact (fzb_beta_lt64 C q s lam (C.enc_lt g hg)).trans (C.dec_enc g hg)
    · rintro ⟨x, hx, hβ⟩
      rw [← hβ]
      change fzbBeta C q s lam x ∈ P
      rw [fzb_beta_lt64 C q s lam hx]
      exact C.dec_mem x hx
  have hZ_eq : ∀ g, g ∈ fourGrp x₁ x₂ ↔ ∃ x < 4, β x = g := by
    intro g
    constructor
    · intro hg
      have hgP : g ∈ P := hZP hg
      refine ⟨C.enc g, (hZ g hgP).mp hg, ?_⟩
      exact (fzb_beta_lt64 C q s lam (by have := (hZ g hgP).mp hg; omega)).trans
        (C.dec_enc g hgP)
    · rintro ⟨x, hx, hβ⟩
      have hx64 : x < 64 := by omega
      rw [← hβ]
      change fzbBeta C q s lam x ∈ fourGrp x₁ x₂
      rw [fzb_beta_lt64 C q s lam hx64]
      exact (hZ (C.dec x) (C.dec_mem x hx64)).mpr (by rw [C.enc_dec x hx64]; exact hx)
  have hsurj : ∀ g ∈ T₂, ∃ x < 1024, β x = g := by
    intro g hg
    obtain ⟨p, hp, w, hw, hg_eq⟩ := fzb_T2_repr hE hP hqT hsT hyT hgen g hg
    refine ⟨64 * w + C.enc p, by have := C.enc_lt p hp; omega, ?_⟩
    change fzbBeta C q s lam (64 * w + C.enc p) = g
    rw [fzb_beta_split C q s lam (C.enc_lt p hp), C.dec_enc p hp, hg_eq]
  have hinj : ∀ x < 1024, ∀ y < 1024, β x = β y → x = y := by
    let f : Fin 1024 → T₂ := fun x => ⟨β x.val, hmem x.val x.isLt⟩
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx, hβ⟩ := hsurj y.val y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hβ⟩
    have hc : Nat.card (Fin 1024) ≤ Nat.card T₂ := by
      rw [Nat.card_fin, hcard]
      norm_num
    have hbi := hf.bijective_of_nat_card_le hc
    intro x hx y hy hxy
    have hsub : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
      apply Subtype.ext
      change β x = β y
      exact hxy
    exact congrArg Fin.val (hbi.1 hsub)
  refine ⟨hmem, hsurj, hinj, ?_, ?_, ?_, ?_, ?_, ?_, hP_eq, hZ_eq⟩
  · unfold fzbBeta
    rw [show (0 : ℕ) % 64 = 0 from rfl, show (0 : ℕ) / 64 = 0 from rfl,
      C.dec_zero, fzb_alpha_zero, mul_one]
  · intro x hx y hy
    exact fzb_beta_mul hE hx hy
  · unfold fzbBeta
    rw [show (64 : ℕ) % 64 = 0 from by norm_num, show (64 : ℕ) / 64 = 1 from by norm_num,
      C.dec_zero, (fzb_alpha_gens q s lam).1, one_mul]
  · unfold fzbBeta
    rw [show (256 : ℕ) % 64 = 0 from by norm_num, show (256 : ℕ) / 64 = 4 from by norm_num,
      C.dec_zero, (fzb_alpha_gens q s lam).2.1, one_mul]
  · unfold fzbBeta
    rw [show (512 : ℕ) % 64 = 0 from by norm_num, show (512 : ℕ) / 64 = 8 from by norm_num,
      C.dec_zero, (fzb_alpha_gens q s lam).2.2.1, one_mul]
  · unfold fzbBeta
    rw [show (128 : ℕ) % 64 = 0 from by norm_num, show (128 : ℕ) / 64 = 2 from by norm_num,
      C.dec_zero, (fzb_alpha_gens q s lam).2.2.2, hq2, one_mul]

end CFSG.OddStandard.SmallF3.FritzII
