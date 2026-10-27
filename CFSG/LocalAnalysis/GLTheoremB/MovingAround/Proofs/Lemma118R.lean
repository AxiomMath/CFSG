module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118Parts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open scoped Pointwise

namespace Lemma118R

@[expose] def Input11_2Alt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ (X B L : Subgroup G), X ≠ ⊤ → IsElemAbelian p B → B ≤ X →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → GLAPComponent p X L →
      ∀ n : ℕ, 10 ≤ n → IsAltType n (barOf p L) → B ≤ Subgroup.normalizer (L : Set G)

@[expose] def Input10_6AltRank : Prop :=
  ∀ (n p : ℕ) (X : Type) [Group X] [Finite X] (K : Subgroup X), 5 ≤ n → p.Prime → p ≠ 2 →
    IsAltType n ↥K →
      (∀ E : Subgroup X, E ≤ K → IsElemAbelian p E → Nat.card E ≤ p ^ (n / p)) ∧
        ∃ E : Subgroup X, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ (n / p)

@[expose] def Input10_5AltMax : Prop :=
  ∀ (n p : ℕ) (X : Type) [Group X] [Finite X] (K : Subgroup X), 5 ≤ n → p.Prime → p ≠ 2 →
    IsAltType n ↥K →
      (∀ E₁ E₂ : Subgroup X, E₁ ≤ K → E₂ ≤ K → IsElemAbelian p E₁ → IsElemAbelian p E₂ →
          Nat.card E₁ = p ^ (n / p) → Nat.card E₂ = p ^ (n / p) →
          ∃ g ∈ K, E₂ = E₁.map (MulAut.conj g).toMonoidHom) ∧
      (∀ y ∈ K, y ^ p = 1 → ∃ E : Subgroup X, E ≤ K ∧ IsElemAbelian p E ∧
          Nat.card E = p ^ (n / p) ∧ y ∈ E)

@[expose] def InputAutAltOdd : Prop :=
  ∀ (n : ℕ) (X : Type) [Group X] [Finite X] (K : Subgroup X), 7 ≤ n → n ≠ 6 →
    IsAltType n ↥K → ∀ g ∈ Subgroup.normalizer (K : Set X), ∀ k : ℕ, Odd k →
      (∀ x ∈ K, g ^ k * x * (g ^ k)⁻¹ = x) → ∃ y ∈ K, ∀ x ∈ K, g * x * g⁻¹ = y * x * y⁻¹

section Facts

variable {H : Type} [Group H] [Finite H]

theorem isPGroup_of_elemAb {p : ℕ} {E : Subgroup H} (hE : IsElemAbelian p E) : IsPGroup p ↥E := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  exact ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g g.2)⟩

theorem card_eq_pow_of_elemAb {p : ℕ} [hp : Fact p.Prime] {E : Subgroup H}
    (hE : IsElemAbelian p E) : ∃ k : ℕ, Nat.card E = p ^ k := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := ↥E)).1 (isPGroup_of_elemAb hE)
  exact ⟨k, hk⟩

theorem card_le_pow_pRank {p : ℕ} [hp : Fact p.Prime] {K E : Subgroup H} (hEK : E ≤ K)
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ CFSG.Open.pRank p K := by
  obtain ⟨k, hk⟩ := card_eq_pow_of_elemAb hE
  rw [hk]
  exact Nat.pow_le_pow_right hp.out.pos (CFSG.SectionRank.le_pRank hp.out.one_lt hEK hE hk)

theorem alt_center_eq_one {n : ℕ} (hn : 5 ≤ n) {K : Subgroup H} (hK : IsAltType n ↥K)
    {z : H} (hz : z ∈ K) (hc : ∀ x ∈ K, z * x = x * z) : z = 1 := by
  obtain ⟨e⟩ := hK
  have hcen : e ⟨z, hz⟩ ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : e.symm g * ⟨z, hz⟩ = ⟨z, hz⟩ * e.symm g :=
      Subtype.ext (by simpa using (hc _ (e.symm g).2).symm)
    have := congrArg e hg
    simpa [map_mul] using this
  have hbot : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  rw [hbot, Subgroup.mem_bot] at hcen
  have : (⟨z, hz⟩ : ↥K) = 1 := e.injective (by rw [hcen, map_one])
  exact congrArg Subtype.val this

@[expose] def cj (g : H) (K : Subgroup H) : Subgroup H := K.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g : H} {K : Subgroup H} {x : H} : x ∈ cj g K ↔ g⁻¹ * x * g ∈ K := by
  unfold cj
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cj_one (K : Subgroup H) : cj 1 K = K := by
  ext x
  rw [mem_cj]
  simp

theorem cj_mul (g h : H) (K : Subgroup H) : cj g (cj h K) = cj (g * h) K := by
  ext x
  rw [mem_cj, mem_cj, mem_cj]
  constructor
  · intro hx
    simpa [mul_assoc] using hx
  · intro hx
    simpa [mul_assoc] using hx

theorem card_sup_of_commute {A B : Subgroup H} (hAB : A ≤ Subgroup.centralizer (B : Set H))
    (hint : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup H) = Nat.card A * Nat.card B := by
  have hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hAB ha) b hb).symm
  let φ : ↥A × ↥B →* H :=
    MonoidHom.mk' (fun x => (x.1 : H) * (x.2 : H)) (by
      intro x y
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
      have h := hc _ y.1.2 _ x.2.2
      simp only [mul_assoc]
      rw [← mul_assoc (y.1 : H) (x.2 : H) (y.2 : H), h]
      simp only [mul_assoc])
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    simp only [φ, MonoidHom.mk'_apply] at h
    have hb : (a : H) = (b : H)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hmem : (a : H) ∈ A ⊓ B := ⟨a.2, hb ▸ B.inv_mem b.2⟩
    rw [hint, Subgroup.mem_bot] at hmem
    have ha1 : a = 1 := Subtype.ext hmem
    have hb1' : (b : H) = 1 := by
      rw [hmem] at hb
      exact (inv_eq_one.1 hb.symm)
    have hb1 : b = 1 := Subtype.ext (by simpa using hb1')
    simp [ha1, hb1]
  have hrange : φ.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · rw [sup_le_iff]
      constructor
      · intro a ha
        exact ⟨(⟨a, ha⟩, 1), by simp [φ]⟩
      · intro b hb
        exact ⟨(1, ⟨b, hb⟩), by simp [φ]⟩
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem comm_of_elemAb {p : ℕ} {B : Subgroup H} (hB : IsElemAbelian p B) {a b : H} (ha : a ∈ B)
    (hb : b ∈ B) : a * b = b * a :=
  congrArg Subtype.val (hB.1.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩)

theorem card_inf_eq_of_normalizes {p m n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 10 ≤ n)
    (hAut : InputAutAltOdd) (hRank : Input10_6AltRank)
    {B K : Subgroup H} (hB : IsElemAbelian p B) (hBcard : Nat.card B = p ^ m)
    (hHm : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ m) (hK : IsAltType n ↥K)
    (hBK : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set H)) :
    Nat.card (B ⊓ K : Subgroup H) = p ^ (n / p) := by
  classical
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  set C : Subgroup H := Subgroup.centralizer (K : Set H) with hCdef
  have hKC : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := fun k hk c hc =>
    Subgroup.mem_centralizer_iff.1 hc k hk
  have hcenter : ∀ z ∈ K, z ∈ C → z = 1 := fun z hz hzC =>
    alt_center_eq_one (by omega) hK hz (fun x hx => (Subgroup.mem_centralizer_iff.1 hzC x hx).symm)
  have hrk := hRank n p H K (by omega) hp.out hp2 hK
  let P₁ : Subgroup H :=
    { carrier := {y | y ∈ K ∧ ∃ c ∈ C, y * c ∈ B}
      one_mem' := ⟨K.one_mem, 1, C.one_mem, by simp [B.one_mem]⟩
      mul_mem' := by
        rintro a b ⟨ha1, c1, hc1, hab1⟩ ⟨hb1, c2, hc2, hab2⟩
        refine ⟨K.mul_mem ha1 hb1, c1 * c2, C.mul_mem hc1 hc2, ?_⟩
        have hcomm : b * c1 = c1 * b := hKC b hb1 c1 hc1
        have hE : a * b * (c1 * c2) = (a * c1) * (b * c2) := by
          calc a * b * (c1 * c2) = a * (b * c1) * c2 := by simp only [mul_assoc]
            _ = a * (c1 * b) * c2 := by rw [hcomm]
            _ = (a * c1) * (b * c2) := by simp only [mul_assoc]
        rw [hE]
        exact B.mul_mem hab1 hab2
      inv_mem' := by
        rintro a ⟨ha1, c1, hc1, hab1⟩
        refine ⟨K.inv_mem ha1, c1⁻¹, C.inv_mem hc1, ?_⟩
        have hac : a * c1 = c1 * a := hKC a ha1 c1 hc1
        have hE : a⁻¹ * c1⁻¹ = (a * c1)⁻¹ := by
          calc a⁻¹ * c1⁻¹ = (c1 * a)⁻¹ := (mul_inv_rev c1 a).symm
            _ = (a * c1)⁻¹ := by rw [hac]
        rw [hE]
        exact B.inv_mem hab1 }
  let P₂ : Subgroup H :=
    { carrier := {c | c ∈ C ∧ ∃ y ∈ K, y * c ∈ B}
      one_mem' := ⟨C.one_mem, 1, K.one_mem, by simp [B.one_mem]⟩
      mul_mem' := by
        rintro c1 c2 ⟨hc1, y1, hy1, hab1⟩ ⟨hc2, y2, hy2, hab2⟩
        refine ⟨C.mul_mem hc1 hc2, y1 * y2, K.mul_mem hy1 hy2, ?_⟩
        have hcomm : y2 * c1 = c1 * y2 := hKC y2 hy2 c1 hc1
        have hE : y1 * y2 * (c1 * c2) = (y1 * c1) * (y2 * c2) := by
          calc y1 * y2 * (c1 * c2) = y1 * (y2 * c1) * c2 := by simp only [mul_assoc]
            _ = y1 * (c1 * y2) * c2 := by rw [hcomm]
            _ = (y1 * c1) * (y2 * c2) := by simp only [mul_assoc]
        rw [hE]
        exact B.mul_mem hab1 hab2
      inv_mem' := by
        rintro c1 ⟨hc1, y1, hy1, hab1⟩
        refine ⟨C.inv_mem hc1, y1⁻¹, K.inv_mem hy1, ?_⟩
        have hyc : y1 * c1 = c1 * y1 := hKC y1 hy1 c1 hc1
        have hE : y1⁻¹ * c1⁻¹ = (y1 * c1)⁻¹ := by
          calc y1⁻¹ * c1⁻¹ = (c1 * y1)⁻¹ := (mul_inv_rev c1 y1).symm
            _ = (y1 * c1)⁻¹ := by rw [hyc]
        rw [hE]
        exact B.inv_mem hab1 }
  have hmemP₁ : ∀ y, y ∈ P₁ ↔ y ∈ K ∧ ∃ c ∈ C, y * c ∈ B := fun y => Iff.rfl
  have hmemP₂ : ∀ c, c ∈ P₂ ↔ c ∈ C ∧ ∃ y ∈ K, y * c ∈ B := fun c => Iff.rfl
  have hdecomp : ∀ b ∈ B, ∃ y ∈ K, ∃ c ∈ C, b = y * c := by
    intro b hb
    have hpow : b ^ p = 1 := hB.2 b hb
    obtain ⟨y, hy, hconj⟩ := hAut n H K (by omega) (by omega) hK b (hBK b hb) p hodd
      (fun x _ => by rw [hpow]; simp)
    refine ⟨y, hy, y⁻¹ * b, ?_, by group⟩
    show y⁻¹ * b ∈ Subgroup.centralizer (K : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hconj x hx
    calc x * (y⁻¹ * b) = y⁻¹ * (y * x * y⁻¹) * b := by group
      _ = y⁻¹ * (b * x * b⁻¹) * b := by rw [h1]
      _ = y⁻¹ * b * x := by group
  have hB_le : B ≤ P₁ ⊔ P₂ := by
    intro b hb
    obtain ⟨y, hy, c, hc, rfl⟩ := hdecomp b hb
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((hmemP₁ y).2 ⟨hy, c, hc, hb⟩))
      (Subgroup.mem_sup_right ((hmemP₂ c).2 ⟨hc, y, hy, hb⟩))
  have hcomm12 : P₁ ≤ Subgroup.centralizer (P₂ : Set H) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hKC y ((hmemP₁ y).1 hy).1 c ((hmemP₂ c).1 hc).1).symm
  have hmeet : ∀ z, z ∈ P₁ → z ∈ P₂ → z = 1 := fun z hz1 hz2 =>
    hcenter z ((hmemP₁ z).1 hz1).1 ((hmemP₂ z).1 hz2).1
  have hint : P₁ ⊓ P₂ = ⊥ := eq_bot_iff.2 fun z hz => by
    rw [Subgroup.mem_bot]; exact hmeet z hz.1 hz.2
  have hpair : ∀ y ∈ K, ∀ y' ∈ K, ∀ c ∈ C, ∀ c' ∈ C, y * c ∈ B → y' * c' ∈ B →
      y * y' = y' * y ∧ c * c' = c' * c := by
    intro y hy y' hy' c hc c' hc' hu hu'
    have hcomm := comm_of_elemAb hB hu hu'
    have hcy' : c * y' = y' * c := (hKC y' hy' c hc).symm
    have hc'y : c' * y = y * c' := (hKC y hy c' hc').symm
    have hE1 : (y * c) * (y' * c') = y * y' * (c * c') := by
      calc (y * c) * (y' * c') = y * (c * y') * c' := by simp only [mul_assoc]
        _ = y * (y' * c) * c' := by rw [hcy']
        _ = y * y' * (c * c') := by simp only [mul_assoc]
    have hE2 : (y' * c') * (y * c) = y' * y * (c' * c) := by
      calc (y' * c') * (y * c) = y' * (c' * y) * c := by simp only [mul_assoc]
        _ = y' * (y * c') * c := by rw [hc'y]
        _ = y' * y * (c' * c) := by simp only [mul_assoc]
    have key : y * y' * (c * c') = y' * y * (c' * c) := by
      rw [← hE1, ← hE2]; exact hcomm
    have hw : (y' * y)⁻¹ * (y * y') = (c' * c) * (c * c')⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      calc (y' * y)⁻¹ * (y * y') * (c * c') = (y' * y)⁻¹ * (y * y' * (c * c')) := by
            simp only [mul_assoc]
        _ = (y' * y)⁻¹ * (y' * y * (c' * c)) := by rw [key]
        _ = c' * c := by group
    have hwC : (y' * y)⁻¹ * (y * y') ∈ C := by
      rw [hw]; exact C.mul_mem (C.mul_mem hc' hc) (C.inv_mem (C.mul_mem hc hc'))
    have hwK : (y' * y)⁻¹ * (y * y') ∈ K :=
      K.mul_mem (K.inv_mem (K.mul_mem hy' hy)) (K.mul_mem hy hy')
    have hw1 : (y' * y)⁻¹ * (y * y') = 1 := hcenter _ hwK hwC
    refine ⟨(inv_mul_eq_one.1 hw1).symm, ?_⟩
    have h2 := hw1
    rw [hw] at h2
    exact (mul_inv_eq_one.1 h2).symm
  have hexp : ∀ y ∈ K, ∀ c ∈ C, y * c ∈ B → y ^ p = 1 ∧ c ^ p = 1 := by
    intro y hy c hc hu
    have hc1 : (y * c) ^ p = 1 := hB.2 _ hu
    have hcm : Commute y c := hKC y hy c hc
    rw [hcm.mul_pow] at hc1
    have hyp : y ^ p ∈ K := K.pow_mem hy p
    have hcp : c ^ p ∈ C := C.pow_mem hc p
    have hyeq : y ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hc1
    have hceq : c ^ p = (y ^ p)⁻¹ := eq_inv_of_mul_eq_one_right hc1
    have h1 : y ^ p = 1 := hcenter _ hyp (by rw [hyeq]; exact C.inv_mem hcp)
    have h2 : c ^ p = 1 := hcenter _ (by rw [hceq]; exact K.inv_mem hyp) hcp
    exact ⟨h1, h2⟩
  have hP₁ : IsElemAbelian p P₁ := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨hx1, c, hc, hxc⟩ := (hmemP₁ _).1 x.2
      obtain ⟨hy1, c', hc', hyc⟩ := (hmemP₁ _).1 y.2
      exact (hpair _ hx1 _ hy1 c hc c' hc' hxc hyc).1
    · obtain ⟨hx1, c, hc, hxc⟩ := (hmemP₁ x).1 hx
      exact (hexp x hx1 c hc hxc).1
  have hP₂ : IsElemAbelian p P₂ := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨hxC, yx, hyx, hxB⟩ := (hmemP₂ _).1 x.2
      obtain ⟨hyC, yy, hyy, hyB⟩ := (hmemP₂ _).1 y.2
      exact (hpair yx hyx yy hyy x hxC y hyC hxB hyB).2
    · obtain ⟨hxC, yx, hyx, hxB⟩ := (hmemP₂ x).1 hx
      exact (hexp yx hyx x hxC hxB).2
  have hsup_ea : IsElemAbelian p (P₁ ⊔ P₂) := isElemAbelian_sup_of_commute hP₁ hP₂ hcomm12
  have hB_eq : B = P₁ ⊔ P₂ := Subgroup.eq_of_le_of_card_ge hB_le (by
    rw [hBcard]
    exact (card_le_pow_pRank le_top hsup_ea).trans (Nat.pow_le_pow_right hp.out.pos hHm))
  have hcardB : Nat.card B = Nat.card P₁ * Nat.card P₂ := by
    rw [hB_eq]; exact card_sup_of_commute hcomm12 hint
  have hBK_eq : B ⊓ K = P₁ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxB, hxK⟩ := Subgroup.mem_inf.1 hx
      rw [hB_eq] at hxB
      obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_of_mem_sup hcomm12 hxB
      have hyK : y ∈ K := ((hmemP₁ y).1 hy).1
      have hcC : c ∈ C := ((hmemP₂ c).1 hc).1
      have hcK : c ∈ K := by simpa using K.mul_mem (K.inv_mem hyK) hxK
      have hc1 : c = 1 := hcenter c hcK hcC
      rw [hc1, mul_one]
      exact hy
    · intro x hx
      refine Subgroup.mem_inf.2 ⟨?_, ((hmemP₁ x).1 hx).1⟩
      rw [hB_eq]
      exact Subgroup.mem_sup_left hx
  have hup : Nat.card P₁ ≤ p ^ (n / p) := hrk.1 P₁ (fun y hy => ((hmemP₁ y).1 hy).1) hP₁
  have hlow : p ^ (n / p) ≤ Nat.card P₁ := by
    obtain ⟨F', hF'K, hF'ea, hF'card⟩ := hrk.2
    have hcomm' : F' ≤ Subgroup.centralizer (P₂ : Set H) := fun x hx =>
      Subgroup.mem_centralizer_iff.2 (fun c hc => (hKC x (hF'K hx) c ((hmemP₂ c).1 hc).1).symm)
    have hint' : F' ⊓ P₂ = ⊥ := eq_bot_iff.2 fun z hz => by
      rw [Subgroup.mem_bot]
      exact hcenter z (hF'K hz.1) ((hmemP₂ z).1 hz.2).1
    have hE : IsElemAbelian p (F' ⊔ P₂) := isElemAbelian_sup_of_commute hF'ea hP₂ hcomm'
    have hEcard : Nat.card (F' ⊔ P₂ : Subgroup H) = p ^ (n / p) * Nat.card P₂ := by
      rw [card_sup_of_commute hcomm' hint', hF'card]
    have hle : Nat.card (F' ⊔ P₂ : Subgroup H) ≤ Nat.card B := by
      rw [hBcard]
      exact (card_le_pow_pRank le_top hE).trans (Nat.pow_le_pow_right hp.out.pos hHm)
    rw [hEcard, hcardB] at hle
    exact Nat.le_of_mul_le_mul_right hle Nat.card_pos
  rw [hBK_eq]
  exact le_antisymm hup hlow


section Products

variable {H : Type} [Group H] [Finite H]

theorem cj_mul_eq (g h : H) (K : Subgroup H) : cj g (cj h K) = cj (g * h) K := cj_mul g h K

theorem cj_inj {g : H} {X Y : Subgroup H} (h : cj g X = cj g Y) : X = Y := by
  have h2 := congrArg (cj g⁻¹) h
  rwa [cj_mul, cj_mul, inv_mul_cancel, cj_one, cj_one] at h2

theorem card_cj (g : H) (K : Subgroup H) : Nat.card (cj g K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isAltType_cj {n : ℕ} (g : H) {K : Subgroup H} (hK : IsAltType n ↥K) :
    IsAltType n ↥(cj g K) := by
  obtain ⟨e⟩ := hK
  exact ⟨(Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩

theorem isElemAbelian_cj {p : ℕ} (g : H) {K : Subgroup H} (hK : IsElemAbelian p K) :
    IsElemAbelian p (cj g K) :=
  CFSG.SectionRank.isElemAbelian_map hK (MulAut.conj g).toMonoidHom

theorem isElemAbelian_mono {p : ℕ} {E F : Subgroup H} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x (hFE hx)⟩
  exact comm_of_elemAb hE (hFE x.2) (hFE y.2)

theorem normalizer_of_cj_eq {g : H} {K : Subgroup H} (h : cj g K = K) :
    g ∈ Subgroup.normalizer (K : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : g * x * g⁻¹ ∈ cj g K ↔ x ∈ K := by
    rw [mem_cj]
    simp [mul_assoc]
  rw [h] at key
  exact key.symm

@[expose] def prodRange (x : ℕ → H) : ℕ → H
  | 0 => 1
  | k + 1 => prodRange x k * x k

theorem prodRange_succ (x : ℕ → H) (k : ℕ) : prodRange x (k + 1) = prodRange x k * x k := rfl

theorem prodRange_succ' (x : ℕ → H) (k : ℕ) :
    prodRange x (k + 1) = x 0 * prodRange (fun j => x (j + 1)) k := by
  induction k with
  | zero => simp [prodRange]
  | succ k ih =>
    rw [prodRange_succ x (k + 1), ih, prodRange_succ (fun j => x (j + 1)) k]
    simp only [mul_assoc]

theorem prodRange_mem {S : Subgroup H} (x : ℕ → H) (k : ℕ) (hx : ∀ j < k, x j ∈ S) :
    prodRange x k ∈ S := by
  induction k with
  | zero => exact S.one_mem
  | succ k ih =>
    rw [prodRange_succ]
    exact S.mul_mem (ih fun j hj => hx j (by omega)) (hx k (by omega))

theorem prodRange_conj (g : H) (x : ℕ → H) (k : ℕ) :
    g * prodRange x k * g⁻¹ = prodRange (fun j => g * x j * g⁻¹) k := by
  induction k with
  | zero => simp [prodRange]
  | succ k ih =>
    rw [prodRange_succ, prodRange_succ]
    calc g * (prodRange x k * x k) * g⁻¹ = (g * prodRange x k * g⁻¹) * (g * x k * g⁻¹) := by
          group
      _ = _ := by rw [ih]

theorem prodRange_comm (w : H) (x : ℕ → H) (k : ℕ) (hw : ∀ j < k, w * x j = x j * w) :
    w * prodRange x k = prodRange x k * w := by
  induction k with
  | zero => simp [prodRange]
  | succ k ih =>
    rw [prodRange_succ]
    have ih' := ih (fun j hj => hw j (by omega))
    calc w * (prodRange x k * x k) = (w * prodRange x k) * x k := by rw [mul_assoc]
      _ = (prodRange x k * w) * x k := by rw [ih']
      _ = prodRange x k * (w * x k) := by rw [mul_assoc]
      _ = prodRange x k * (x k * w) := by rw [hw k (by omega)]
      _ = prodRange x (k + 1) * w := by rw [prodRange_succ, mul_assoc]

theorem prodRange_mul (x y : ℕ → H) (k : ℕ)
    (hxy : ∀ i < k, ∀ j < k, i ≠ j → x i * y j = y j * x i) :
    prodRange x k * prodRange y k = prodRange (fun j => x j * y j) k := by
  induction k with
  | zero => simp [prodRange]
  | succ k ih =>
    have hcomm : x k * prodRange y k = prodRange y k * x k :=
      prodRange_comm (x k) y k (fun j hj => hxy k (by omega) j (by omega) (by omega))
    have ih' := ih (fun i hi j hj hne => hxy i (by omega) j (by omega) hne)
    rw [prodRange_succ x k, prodRange_succ y k, prodRange_succ (fun j => x j * y j) k]
    calc prodRange x k * x k * (prodRange y k * y k)
        = prodRange x k * (x k * prodRange y k) * y k := by simp only [mul_assoc]
      _ = prodRange x k * (prodRange y k * x k) * y k := by rw [hcomm]
      _ = (prodRange x k * prodRange y k) * (x k * y k) := by simp only [mul_assoc]
      _ = prodRange (fun j => x j * y j) k * (x k * y k) := by rw [ih']

theorem prodRange_split (h : ℕ → H) (C : Subgroup H) (j : ℕ) :
    ∀ k : ℕ, (∀ i < k, i ≠ j → h i ∈ C) →
      (k ≤ j → prodRange h k ∈ C) ∧
        (j < k → ∃ A ∈ C, ∃ B ∈ C, prodRange h k = A * h j * B) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun _ => by simp [prodRange, C.one_mem], fun hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hh
    have ih' := ih (fun i hi hne => hh i (by omega) hne)
    have hkC : k ≠ j → h k ∈ C := fun hne => hh k (by omega) hne
    refine ⟨fun hkj => ?_, fun hjk => ?_⟩
    · rw [prodRange_succ]
      exact C.mul_mem (ih'.1 (by omega)) (hkC (by omega))
    · rcases Nat.lt_or_ge j k with hlt | hge
      · obtain ⟨A, hA, B, hB, hAB⟩ := ih'.2 hlt
        refine ⟨A, hA, B * h k, C.mul_mem hB (hkC (by omega)), ?_⟩
        rw [prodRange_succ, hAB]
        simp only [mul_assoc]
      · have hjk' : j = k := by omega
        refine ⟨prodRange h k, ih'.1 (by omega), 1, C.one_mem, ?_⟩
        rw [prodRange_succ, mul_one, hjk']

end Products

section Orbit

variable {H : Type} [Group H] [Finite H]

@[expose] def Icof (a : H) (Ĩ : Subgroup H) (j : ℕ) : Subgroup H := cj (a ^ j) Ĩ

theorem Icof_zero (a : H) (Ĩ : Subgroup H) : Icof a Ĩ 0 = Ĩ := by
  simp [Icof, cj_one]

theorem cj_Icof (a : H) (Ĩ : Subgroup H) (i j : ℕ) :
    cj (a ^ i) (Icof a Ĩ j) = Icof a Ĩ (i + j) := by
  unfold Icof
  rw [cj_mul_eq, ← pow_add]

theorem Icof_add_period {a : H} {Ĩ : Subgroup H} {p : ℕ} (ha : a ^ p = 1) (j : ℕ) :
    Icof a Ĩ (j + p) = Icof a Ĩ j := by
  unfold Icof
  rw [pow_add, ha, mul_one]

theorem Icof_period {a : H} {Ĩ : Subgroup H} {p : ℕ} (ha : a ^ p = 1) (j s : ℕ) :
    Icof a Ĩ (j + p * s) = Icof a Ĩ j := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show j + p * (s + 1) = (j + p * s) + p by ring, Icof_add_period ha, ih]

theorem Icof_one_eq_zero_of_eq {a : H} {Ĩ : Subgroup H} {p : ℕ} [hp : Fact p.Prime]
    (ha : a ^ p = 1) {k : ℕ} (hk0 : 0 < k) (hkp : k < p) (hk : Icof a Ĩ k = Icof a Ĩ 0) :
    Icof a Ĩ 1 = Icof a Ĩ 0 := by
  have hmul : ∀ t : ℕ, Icof a Ĩ (k * t) = Icof a Ĩ 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.mul_succ, ← cj_Icof a Ĩ (k * t) k, hk, cj_Icof, add_zero, ih]
  have hcop : Nat.Coprime k p :=
    (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      (Nat.not_dvd_of_pos_of_lt hk0 hkp))
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  have h2 := Icof_period (Ĩ := Ĩ) ha (k * t % p) (k * t / p)
  rw [Nat.mod_add_div, ht] at h2
  rw [← h2, hmul t]

theorem Icof_ne_of_lt {a : H} {Ĩ : Subgroup H} {p : ℕ} [hp : Fact p.Prime] (ha : a ^ p = 1)
    (hne : Icof a Ĩ 1 ≠ Icof a Ĩ 0) {i j : ℕ} (hij : i < j) (hj : j < p)
    (heq : Icof a Ĩ i = Icof a Ĩ j) : False := by
  apply hne
  have h1 : cj (a ^ i) (Icof a Ĩ (j - i)) = Icof a Ĩ j := by
    rw [cj_Icof, show i + (j - i) = j by omega]
  have h2 : cj (a ^ i) Ĩ = cj (a ^ i) (Icof a Ĩ (j - i)) := by
    have : Icof a Ĩ i = cj (a ^ i) Ĩ := rfl
    rw [← this, heq, h1]
  have h3 : Icof a Ĩ (j - i) = Ĩ := (cj_inj h2).symm
  apply Icof_one_eq_zero_of_eq ha (k := j - i) (by omega) (by omega)
  rw [h3, Icof_zero]

theorem Icof_ne {a : H} {Ĩ : Subgroup H} {p : ℕ} [hp : Fact p.Prime] (ha : a ^ p = 1)
    (hne : Icof a Ĩ 1 ≠ Icof a Ĩ 0) {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) :
    Icof a Ĩ i ≠ Icof a Ĩ j := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact fun heq => Icof_ne_of_lt ha hne h hj heq
  · exact fun heq => Icof_ne_of_lt ha hne h hi heq.symm

theorem le_Icof_of_le {a : H} {Ĩ F : Subgroup H} (j : ℕ) (hF : F ≤ Ĩ) :
    cj (a ^ j) F ≤ Icof a Ĩ j := by
  intro x hx
  rw [mem_cj] at hx
  unfold Icof
  rw [mem_cj]
  exact hF hx

end Orbit

end Facts

section Core

variable {H : Type} [Group H] [Finite H]

theorem core_caseA {p m n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 10 ≤ n)
    (hAut : InputAutAltOdd) (hRank : Input10_6AltRank) (hMax : Input10_5AltMax)
    (hHm : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ m)
    {B₀ : Subgroup H} (hB₀ : IsElemAbelian p B₀) (hB₀card : Nat.card B₀ = p ^ m)
    {a : H} (ha : a ^ p = 1) {Ĩ : Subgroup H} (hĨ : IsAltType n ↥Ĩ)
    (hnorm : ∀ j : ℕ, B₀ ≤ Subgroup.normalizer ((Icof a Ĩ j : Subgroup H) : Set H))
    (hA : Icof a Ĩ 1 = Icof a Ĩ 0) :
    ∃ (h : H) (D : Subgroup H), IsElemAbelian p D ∧ Nat.card D = p ^ (n / p) ∧
      (∀ d ∈ D, d ∈ B₀.map (MulAut.conj h).toMonoidHom) ∧ ∀ d ∈ D, a * d = d * a := by
  classical
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hK : IsAltType n ↥(Icof a Ĩ 0) := by
    rw [Icof_zero]; exact hĨ
  have hproj : Nat.card (B₀ ⊓ Icof a Ĩ 0 : Subgroup H) = p ^ (n / p) :=
    card_inf_eq_of_normalizes hp2 hn hAut hRank hB₀ hB₀card hHm hK (fun b hb => hnorm 0 hb)
  have haN : a ∈ Subgroup.normalizer ((Icof a Ĩ 0 : Subgroup H) : Set H) := by
    apply normalizer_of_cj_eq
    have h1 : cj (a ^ 1) (Icof a Ĩ 0) = Icof a Ĩ 0 := by
      rw [cj_Icof, add_zero, hA]
    simpa using h1
  obtain ⟨y, hy, hconj⟩ := hAut n H (Icof a Ĩ 0) (by omega) (by omega) hK a haN p hodd
    (fun x _ => by rw [ha]; simp)
  have hpow : ∀ k : ℕ, ∀ x ∈ Icof a Ĩ 0, a ^ k * x * (a ^ k)⁻¹ = y ^ k * x * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      have hz : y ^ k * x * (y ^ k)⁻¹ ∈ Icof a Ĩ 0 :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hy k) hx)
          (Subgroup.inv_mem _ (Subgroup.pow_mem _ hy k))
      calc a ^ (k + 1) * x * (a ^ (k + 1))⁻¹ = a * (a ^ k * x * (a ^ k)⁻¹) * a⁻¹ := by
            rw [pow_succ']; group
        _ = a * (y ^ k * x * (y ^ k)⁻¹) * a⁻¹ := by rw [ih x hx]
        _ = y * (y ^ k * x * (y ^ k)⁻¹) * y⁻¹ := hconj _ hz
        _ = y ^ (k + 1) * x * (y ^ (k + 1))⁻¹ := by rw [pow_succ']; group
  have hycent : ∀ x ∈ Icof a Ĩ 0, y ^ p * x = x * y ^ p := by
    intro x hx
    have h1 := hpow p x hx
    rw [ha, one_mul, inv_one, mul_one] at h1
    calc y ^ p * x = (y ^ p * x * (y ^ p)⁻¹) * y ^ p := by group
      _ = x * y ^ p := by rw [← h1]
  have hyp1 : y ^ p = 1 :=
    alt_center_eq_one (by omega) hK (Subgroup.pow_mem _ hy p) (fun x hx => hycent x hx)
  obtain ⟨E, hEK, hEea, hEcard, hyE⟩ :=
    (hMax n p H (Icof a Ĩ 0) (by omega) hp.out hp2 hK).2 y hy hyp1
  have hEcomm : ∀ x ∈ E, a * x = x * a := by
    intro x hx
    have h1 := hconj x (hEK hx)
    have h2 : y * x * y⁻¹ = x := by
      rw [comm_of_elemAb hEea hyE hx]; group
    rw [h2] at h1
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x * a := by rw [h1]
  obtain ⟨g, -, hgE⟩ := (hMax n p H (Icof a Ĩ 0) (by omega) hp.out hp2 hK).1
    (B₀ ⊓ Icof a Ĩ 0) E inf_le_right hEK (isElemAbelian_mono hB₀ inf_le_left) hEea hproj hEcard
  refine ⟨g, E, hEea, hEcard, ?_, hEcomm⟩
  intro d hd
  rw [hgE] at hd
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hd
  exact Subgroup.mem_map.2 ⟨b, (Subgroup.mem_inf.1 hb).1, rfl⟩

theorem core_caseB {p m n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 10 ≤ n)
    (hAut : InputAutAltOdd) (hRank : Input10_6AltRank) (hMax : Input10_5AltMax)
    (hHm : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ m)
    {B₀ : Subgroup H} (hB₀ : IsElemAbelian p B₀) (hB₀card : Nat.card B₀ = p ^ m)
    {a : H} (ha : a ^ p = 1) {Ĩ : Subgroup H} (hĨ : IsAltType n ↥Ĩ)
    (hnorm : ∀ j : ℕ, B₀ ≤ Subgroup.normalizer ((Icof a Ĩ j : Subgroup H) : Set H))
    (hcomm : ∀ i j : ℕ, Icof a Ĩ i ≠ Icof a Ĩ j →
      ∀ x ∈ Icof a Ĩ i, ∀ y ∈ Icof a Ĩ j, x * y = y * x)
    (hne : Icof a Ĩ 1 ≠ Icof a Ĩ 0) :
    ∃ (h : H) (D : Subgroup H), IsElemAbelian p D ∧ Nat.card D = p ^ (n / p) ∧
      (∀ d ∈ D, d ∈ B₀.map (MulAut.conj h).toMonoidHom) ∧ ∀ d ∈ D, a * d = d * a := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hcommB : ∀ i < p, ∀ j < p, i ≠ j → ∀ x ∈ Icof a Ĩ i, ∀ y ∈ Icof a Ĩ j, x * y = y * x :=
    fun i hi j hj hij => hcomm i j (Icof_ne ha hne hi hj hij)
  have hIalt : ∀ j, IsAltType n ↥(Icof a Ĩ j) := fun j => isAltType_cj (a ^ j) hĨ
  have hproj : ∀ j, Nat.card (B₀ ⊓ Icof a Ĩ j : Subgroup H) = p ^ (n / p) := fun j =>
    card_inf_eq_of_normalizes hp2 hn hAut hRank hB₀ hB₀card hHm (hIalt j) (fun b hb => hnorm j hb)
  obtain ⟨F₀, hF₀K, hF₀ea, hF₀card⟩ :=
    (hRank n p H (Icof a Ĩ 0) (by omega) hp.out hp2 (hIalt 0)).2
  have hF₀Ĩ : F₀ ≤ Ĩ := by rw [← Icof_zero a Ĩ]; exact hF₀K
  have hFj : ∀ j, ∃ g ∈ Icof a Ĩ j, cj (a ^ j) F₀ =
      (B₀ ⊓ Icof a Ĩ j).map (MulAut.conj g).toMonoidHom := fun j =>
    (hMax n p H (Icof a Ĩ j) (by omega) hp.out hp2 (hIalt j)).1 (B₀ ⊓ Icof a Ĩ j) (cj (a ^ j) F₀)
      inf_le_right (le_Icof_of_le j hF₀Ĩ) (isElemAbelian_mono hB₀ inf_le_left)
      (isElemAbelian_cj _ hF₀ea) (hproj j) (by rw [card_cj, hF₀card])
  choose hj hjmem hjeq using hFj
  have hsplit : ∀ j < p, ∀ y ∈ Icof a Ĩ j,
      prodRange hj p * y * (prodRange hj p)⁻¹ = hj j * y * (hj j)⁻¹ := by
    intro j hj_lt y hy
    have hC : ∀ i < p, i ≠ j → hj i ∈ Subgroup.centralizer (Icof a Ĩ j : Set H) := by
      intro i hi hij
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hcommB i hi j hj_lt hij (hj i) (hjmem i) z hz).symm
    obtain ⟨A, hA, B', hB', hAB⟩ := (prodRange_split hj
      (Subgroup.centralizer (Icof a Ĩ j : Set H)) j p (fun i hi hne' => hC i hi hne')).2 hj_lt
    rw [hAB]
    have hy' : hj j * y * (hj j)⁻¹ ∈ Icof a Ĩ j :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hjmem j) hy) (Subgroup.inv_mem _ (hjmem j))
    have hA' := Subgroup.mem_centralizer_iff.1 hA _ hy'
    have hB'' := Subgroup.mem_centralizer_iff.1 hB' y hy
    have e1 : B' * y * B'⁻¹ = y := by rw [← hB'']; group
    have e2 : A * (hj j * y * (hj j)⁻¹) * A⁻¹ = hj j * y * (hj j)⁻¹ := by
      rw [← hA']; group
    calc A * hj j * B' * y * (A * hj j * B')⁻¹
        = A * (hj j * (B' * y * B'⁻¹) * (hj j)⁻¹) * A⁻¹ := by group
      _ = A * (hj j * y * (hj j)⁻¹) * A⁻¹ := by rw [e1]
      _ = hj j * y * (hj j)⁻¹ := e2
  have hFsub : ∀ j < p, ∀ x ∈ cj (a ^ j) F₀,
      x ∈ B₀.map (MulAut.conj (prodRange hj p)).toMonoidHom := by
    intro j hj_lt x hx
    rw [hjeq j] at hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨b, (Subgroup.mem_inf.1 hb).1, ?_⟩
    show prodRange hj p * b * (prodRange hj p)⁻¹ = hj j * b * (hj j)⁻¹
    exact hsplit j hj_lt b (Subgroup.mem_inf.1 hb).2
  have hfac_cj : ∀ x ∈ F₀, ∀ j : ℕ, a ^ j * x * (a ^ j)⁻¹ ∈ cj (a ^ j) F₀ := by
    intro x hx j
    rw [mem_cj]
    convert hx using 1
    group
  have hfac : ∀ x ∈ F₀, ∀ j : ℕ, a ^ j * x * (a ^ j)⁻¹ ∈ Icof a Ĩ j := fun x hx j =>
    le_Icof_of_le j hF₀Ĩ (hfac_cj x hx j)
  have hcomm_fac : ∀ x ∈ F₀, ∀ x' ∈ F₀, ∀ i < p, ∀ j < p, i ≠ j →
      (a ^ i * x * (a ^ i)⁻¹) * (a ^ j * x' * (a ^ j)⁻¹) =
        (a ^ j * x' * (a ^ j)⁻¹) * (a ^ i * x * (a ^ i)⁻¹) :=
    fun x hx x' hx' i hi j hj_lt hij =>
      hcommB i hi j hj_lt hij _ (hfac x hx i) _ (hfac x' hx' j)
  have hδmul : ∀ x ∈ F₀, ∀ x' ∈ F₀,
      prodRange (fun j => a ^ j * (x * x') * (a ^ j)⁻¹) p =
        prodRange (fun j => a ^ j * x * (a ^ j)⁻¹) p *
          prodRange (fun j => a ^ j * x' * (a ^ j)⁻¹) p := by
    intro x hx x' hx'
    rw [prodRange_mul _ _ p (fun i hi j hj_lt hij => hcomm_fac x hx x' hx' i hi j hj_lt hij)]
    congr 1
    funext j
    group
  let δ : ↥F₀ →* H := MonoidHom.mk'
    (fun x => prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p) (by
      intro x x'
      simp only [Subgroup.coe_mul]
      exact hδmul x.1 x.2 x'.1 x'.2)
  have hsplit_head : ∀ x ∈ F₀, prodRange (fun j => a ^ j * x * (a ^ j)⁻¹) p =
      x * prodRange (fun j => a ^ (j + 1) * x * (a ^ (j + 1))⁻¹) (p - 1) := by
    intro x hx
    have h1 := prodRange_succ' (fun j => a ^ j * x * (a ^ j)⁻¹) (p - 1)
    rw [Nat.sub_add_cancel hp1.le] at h1
    rw [h1]
    simp only [pow_zero, one_mul, inv_one, mul_one]
  have hQcent : ∀ x ∈ F₀, ∀ w ∈ Icof a Ĩ 0,
      w * prodRange (fun j => a ^ (j + 1) * x * (a ^ (j + 1))⁻¹) (p - 1) =
        prodRange (fun j => a ^ (j + 1) * x * (a ^ (j + 1))⁻¹) (p - 1) * w := by
    intro x hx w hw
    apply prodRange_comm w _ (p - 1)
    intro j hj
    exact hcommB 0 (by omega) (j + 1) (by omega) (by omega) w hw _ (hfac x hx (j + 1))
  have hδinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro x hx1
    have hxF : (x : H) ∈ F₀ := x.2
    have hx1' : prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p = 1 := hx1
    rw [hsplit_head x hxF] at hx1'
    have hQ : prodRange (fun j => a ^ (j + 1) * (x : H) * (a ^ (j + 1))⁻¹) (p - 1) =
        (x : H)⁻¹ := eq_inv_of_mul_eq_one_right hx1'
    apply Subtype.ext
    refine alt_center_eq_one (by omega) (hIalt 0) (hF₀K hxF) ?_
    intro w hw
    have hc := hQcent x hxF w hw
    rw [hQ] at hc
    calc (x : H) * w = (x : H) * (w * (x : H)⁻¹) * (x : H) := by group
      _ = (x : H) * ((x : H)⁻¹ * w) * (x : H) := by rw [hc]
      _ = w * (x : H) := by group
  have hDea : IsElemAbelian p δ.range := by
    have hcommD : ∀ u ∈ δ.range, ∀ v ∈ δ.range, u * v = v * u := by
      rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (comm_of_elemAb hF₀ea x.2 x'.2)
    refine ⟨⟨⟨fun u v => Subtype.ext (hcommD u u.2 v v.2)⟩⟩, fun u hu => ?_⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hu
    rw [← map_pow, show x ^ p = 1 from Subtype.ext (by simpa using hF₀ea.2 x.1 x.2), map_one]
  have hDcard : Nat.card δ.range = p ^ (n / p) := by
    rw [← hF₀card]
    exact (Nat.card_congr (MonoidHom.ofInjective hδinj).toEquiv).symm
  have hDS : ∀ d ∈ δ.range, d ∈ B₀.map (MulAut.conj (prodRange hj p)).toMonoidHom := by
    rintro _ ⟨x, rfl⟩
    exact prodRange_mem _ p (fun j hj_lt => hFsub j hj_lt _ (hfac_cj x x.2 j))
  have hDcent : ∀ d ∈ δ.range, a * d = d * a := by
    rintro _ ⟨x, rfl⟩
    show a * prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p =
      prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p * a
    have hx := x.2
    have e1 : a * prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p * a⁻¹ =
        prodRange (fun j => a ^ (j + 1) * (x : H) * (a ^ (j + 1))⁻¹) p := by
      rw [prodRange_conj]
      congr 1
      funext j
      beta_reduce
      rw [pow_succ']
      group
    have e2 : prodRange (fun j => a ^ (j + 1) * (x : H) * (a ^ (j + 1))⁻¹) p =
        prodRange (fun j => a ^ (j + 1) * (x : H) * (a ^ (j + 1))⁻¹) (p - 1) * (x : H) := by
      have hgp : a ^ (p - 1 + 1) * (x : H) * (a ^ (p - 1 + 1))⁻¹ = (x : H) := by
        rw [Nat.sub_add_cancel hp1.le, ha]; simp
      have h1 := prodRange_succ (fun j => a ^ (j + 1) * (x : H) * (a ^ (j + 1))⁻¹) (p - 1)
      beta_reduce at h1
      rw [hgp] at h1
      rw [Nat.sub_add_cancel hp1.le] at h1
      exact h1
    have hsh := hsplit_head x hx
    have hcQ := hQcent x hx x (hF₀K hx)
    have key : a * prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p * a⁻¹ =
        prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p := by
      rw [e1, e2, hsh]
      exact hcQ.symm
    calc a * prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p
        = (a * prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p * a⁻¹) * a := by group
      _ = prodRange (fun j => a ^ j * (x : H) * (a ^ j)⁻¹) p * a := by rw [key]
  exact ⟨prodRange hj p, δ.range, hDea, hDcard, hDS, hDcent⟩

theorem core_exists {p m n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 10 ≤ n)
    (hAut : InputAutAltOdd) (hRank : Input10_6AltRank) (hMax : Input10_5AltMax)
    (hHm : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ m)
    {B₀ : Subgroup H} (hB₀ : IsElemAbelian p B₀) (hB₀card : Nat.card B₀ = p ^ m)
    {a : H} (ha : a ^ p = 1) {Ĩ : Subgroup H} (hĨ : IsAltType n ↥Ĩ)
    (hnorm : ∀ j : ℕ, B₀ ≤ Subgroup.normalizer ((Icof a Ĩ j : Subgroup H) : Set H))
    (hcomm : ∀ i j : ℕ, Icof a Ĩ i ≠ Icof a Ĩ j →
      ∀ x ∈ Icof a Ĩ i, ∀ y ∈ Icof a Ĩ j, x * y = y * x) :
    ∃ (h : H) (D : Subgroup H), IsElemAbelian p D ∧ Nat.card D = p ^ (n / p) ∧
      (∀ d ∈ D, d ∈ B₀.map (MulAut.conj h).toMonoidHom) ∧ ∀ d ∈ D, a * d = d * a := by
  by_cases hA : Icof a Ĩ 1 = Icof a Ĩ 0
  · exact core_caseA hp2 hn hAut hRank hMax hHm hB₀ hB₀card ha hĨ hnorm hA
  · exact core_caseB hp2 hn hAut hRank hMax hHm hB₀ hB₀card ha hĨ hnorm hcomm hA

end Core


section Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem card_comap_quot (P : Subgroup Y) [P.Normal] (K : Subgroup (Y ⧸ P)) :
    Nat.card (K.comap (QuotientGroup.mk' P)) = Nat.card K * Nat.card P := by
  have h1 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' P))
  have h2 := Subgroup.card_mul_index K
  have h3 := Subgroup.index_comap_of_surjective (H := K) (QuotientGroup.mk'_surjective P)
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup P
  have hidx : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h3] at h1
  have key : Nat.card (K.comap (QuotientGroup.mk' P)) * K.index =
      (Nat.card K * Nat.card P) * K.index := by
    rw [h1, h4, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx) key

theorem card_map_eq_of_inf_bot (P : Subgroup Y) [P.Normal] {S : Subgroup Y} (hS : S ⊓ P = ⊥) :
    Nat.card (S.map (QuotientGroup.mk' P)) = Nat.card S := by
  have hf : Function.Injective ((QuotientGroup.mk' P).comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx2 : QuotientGroup.mk' P (x : Y) = 1 := hx
    have hxP : (x : Y) ∈ P := (QuotientGroup.eq_one_iff _).1 hx2
    have hxSP : (x : Y) ∈ S ⊓ P := ⟨x.2, hxP⟩
    rw [hS, Subgroup.mem_bot] at hxSP
    exact Subtype.ext hxSP
  have hr : ((QuotientGroup.mk' P).comp S.subtype).range = S.map (QuotientGroup.mk' P) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem inf_eq_bot_of_pgroup {p : ℕ} [hp : Fact p.Prime] {Q P : Subgroup Y} (hQ : IsPGroup p Q)
    (hP : ¬ p ∣ Nat.card P) : Q ⊓ P = ⊥ := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p) (G := ↥(Q ⊓ P))).1 hQ.to_inf_left
  have hdvd : Nat.card ↥(Q ⊓ P) ∣ Nat.card P := Subgroup.card_dvd_of_le inf_le_right
  rw [hj] at hdvd
  have hj0 : j = 0 := by
    by_contra hne
    exact hP ((dvd_pow_self p hne).trans hdvd)
  rw [hj0, pow_zero] at hj
  exact Subgroup.eq_bot_of_card_eq _ hj

theorem isElemAbelian_of_map {p : ℕ} (P : Subgroup Y) [P.Normal] {S : Subgroup Y}
    (hS : S ⊓ P = ⊥) (hSD : IsElemAbelian p (S.map (QuotientGroup.mk' P))) :
    IsElemAbelian p S := by
  have hinj : ∀ u ∈ S, ∀ v ∈ S, QuotientGroup.mk' P u = QuotientGroup.mk' P v → u = v := by
    intro u hu v hv huv
    have h1 : u⁻¹ * v ∈ P := QuotientGroup.eq.1 huv
    have h2 : u⁻¹ * v ∈ S ⊓ P := ⟨S.mul_mem (S.inv_mem hu) hv, h1⟩
    rw [hS, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.1 h2
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · apply hinj (x * y) (S.mul_mem x.2 y.2) (y * x) (S.mul_mem y.2 x.2)
    have hc : QuotientGroup.mk' P x * QuotientGroup.mk' P y =
        QuotientGroup.mk' P y * QuotientGroup.mk' P x :=
      congrArg Subtype.val (hSD.1.is_comm.comm
        (⟨_, Subgroup.mem_map_of_mem _ x.2⟩ : ↥(S.map (QuotientGroup.mk' P)))
        ⟨_, Subgroup.mem_map_of_mem _ y.2⟩)
    rw [map_mul, map_mul]
    exact hc
  · apply hinj (x ^ p) (S.pow_mem hx p) 1 S.one_mem
    rw [map_pow, map_one]
    exact hSD.2 _ (Subgroup.mem_map_of_mem _ hx)

theorem pow_eq_one_of_mem_zpowers {x : Y} {p : ℕ} (hx : x ^ p = 1) {y : Y}
    (hy : y ∈ Subgroup.zpowers x) : y ^ p = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem fact_pow_mul {p k m : ℕ} [hp : Fact p.Prime] (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    (p ^ k * m).factorization p = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

end Lift


section LiftMain

variable {Y : Type} [Group Y] [Finite Y]

theorem lift_elemAb {p : ℕ} [hp : Fact p.Prime] (P : Subgroup Y) [P.Normal]
    (hP : ¬ p ∣ Nat.card P)
    {Bm : Subgroup Y} (hBm : IsElemAbelian p Bm) (hBmP : Bm ⊓ P = ⊥)
    {a : Y} (ha : a ^ p = 1)
    {D : Subgroup (Y ⧸ P)} (hD : IsElemAbelian p D)
    (haD : ∀ d ∈ D, QuotientGroup.mk' P a * d = d * QuotientGroup.mk' P a)
    {x₀ : Y} (hDB : ∀ d ∈ D, ∃ b ∈ Bm, d = QuotientGroup.mk' P (x₀ * b * x₀⁻¹)) :
    ∃ x : Y, ∃ F : Subgroup Y, IsElemAbelian p F ∧ Nat.card F = Nat.card D ∧
      (∀ f ∈ F, ∃ b ∈ Bm, f = x * b * x⁻¹) ∧ ∀ f ∈ F, a * f = f * a := by
  classical
  have hconj_apply : ∀ b : Y, (MulAut.conj x₀).toMonoidHom b = x₀ * b * x₀⁻¹ := fun b => rfl
  have hzpow : IsPGroup p (Subgroup.zpowers (QuotientGroup.mk' P a)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, ha, map_one]
  have hDp : IsPGroup p D := isPGroup_of_elemAb hD
  have hzN : Subgroup.zpowers (QuotientGroup.mk' P a) ≤
      Subgroup.normalizer (D : Set (Y ⧸ P)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hd
      have e : QuotientGroup.mk' P a * d * (QuotientGroup.mk' P a)⁻¹ = d := by
        rw [haD d hd]; group
      rw [e]; exact hd
    · intro hd
      have hcomm_u := haD _ hd
      have key : (QuotientGroup.mk' P a)⁻¹ *
          (QuotientGroup.mk' P a * d * (QuotientGroup.mk' P a)⁻¹) * QuotientGroup.mk' P a =
          QuotientGroup.mk' P a * d * (QuotientGroup.mk' P a)⁻¹ := by
        calc _ = (QuotientGroup.mk' P a)⁻¹ *
              ((QuotientGroup.mk' P a * d * (QuotientGroup.mk' P a)⁻¹) * QuotientGroup.mk' P a) := by
              group
          _ = (QuotientGroup.mk' P a)⁻¹ *
              (QuotientGroup.mk' P a * (QuotientGroup.mk' P a * d * (QuotientGroup.mk' P a)⁻¹)) := by
              rw [hcomm_u]
          _ = _ := by group
      have hd' : d = (QuotientGroup.mk' P a)⁻¹ *
          (QuotientGroup.mk' P a * d * (QuotientGroup.mk' P a)⁻¹) * QuotientGroup.mk' P a := by
        group
      rw [key] at hd'
      rw [hd']; exact hd
  have hKp : IsPGroup p ↥(Subgroup.zpowers (QuotientGroup.mk' P a) ⊔ D) :=
    IsPGroup.to_sup_of_normal_right' hzpow hDp hzN
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).1 hKp
  set K : Subgroup (Y ⧸ P) := Subgroup.zpowers (QuotientGroup.mk' P a) ⊔ D with hKdef
  have haK : QuotientGroup.mk' P a ∈ K := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hDK : D ≤ K := le_sup_right
  set X' : Subgroup Y := K.comap (QuotientGroup.mk' P) with hX'def
  have haX' : a ∈ X' := haK
  have hX'card : Nat.card X' = p ^ k * Nat.card P := by
    rw [hX'def, card_comap_quot, hk]
  have haXp : IsPGroup p ↥((Subgroup.zpowers a).subgroupOf X') := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    apply Subtype.ext
    simpa using pow_eq_one_of_mem_zpowers ha (Subgroup.mem_subgroupOf.1 g.2)
  obtain ⟨Q₀, hQ₀⟩ := IsPGroup.exists_le_sylow haXp
  have hQ₀card : Nat.card Q₀ = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hX'card, fact_pow_mul hP (Nat.card_pos.ne')]
  set Q : Subgroup Y := (Q₀ : Subgroup X').map X'.subtype with hQdef
  have hQp : IsPGroup p Q := IsPGroup.map Q₀.isPGroup' X'.subtype
  have hQcard : Nat.card Q = p ^ k := by
    rw [hQdef, Subgroup.card_map_of_injective Subtype.val_injective, ← hQ₀card]
  have haQ : a ∈ Q := by
    apply Subgroup.mem_map.2
    exact ⟨⟨a, haX'⟩, hQ₀ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers a)), rfl⟩
  have hQX' : Q ≤ X' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hQP : Q ⊓ P = ⊥ := inf_eq_bot_of_pgroup hQp hP
  have hQmap : Q.map (QuotientGroup.mk' P) = K := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_comap.1 (hQX' hy)
    · rw [card_map_eq_of_inf_bot P hQP, hQcard, hk]
  set W : Subgroup Y := D.comap (QuotientGroup.mk' P) with hWdef
  set F : Subgroup Y := Q ⊓ W with hFdef
  have hFmap : F.map (QuotientGroup.mk' P) = D := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hx).2
    · intro d hd
      have hdQ : d ∈ Q.map (QuotientGroup.mk' P) := by
        rw [hQmap]; exact hDK hd
      obtain ⟨q, hq, hqd⟩ := Subgroup.mem_map.1 hdQ
      refine Subgroup.mem_map.2 ⟨q, Subgroup.mem_inf.2 ⟨hq, ?_⟩, hqd⟩
      exact Subgroup.mem_comap.2 (by rw [hqd]; exact hd)
  have hFP : F ⊓ P = ⊥ := by
    apply eq_bot_iff.2
    have h := inf_le_inf_right P (inf_le_left : F ≤ Q)
    rw [hQP] at h
    exact h
  have hFD : Nat.card F = Nat.card D := by
    rw [← card_map_eq_of_inf_bot P hFP, hFmap]
  have hFea : IsElemAbelian p F := isElemAbelian_of_map P hFP (by rw [hFmap]; exact hD)
  have hinjQ : ∀ u ∈ Q, ∀ v ∈ Q, QuotientGroup.mk' P u = QuotientGroup.mk' P v → u = v := by
    intro u hu v hv huv
    have h1 : u⁻¹ * v ∈ P := QuotientGroup.eq.1 huv
    have h2 : u⁻¹ * v ∈ Q ⊓ P := ⟨Q.mul_mem (Q.inv_mem hu) hv, h1⟩
    rw [hQP, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.1 h2
  have hcent : ∀ f ∈ F, a * f = f * a := by
    intro f hf
    have hfQ : f ∈ Q := (Subgroup.mem_inf.1 hf).1
    have hfD : QuotientGroup.mk' P f ∈ D := Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hf).2
    have haQf : a * f * a⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem haQ hfQ) (Q.inv_mem haQ)
    have himg : QuotientGroup.mk' P (a * f * a⁻¹) = QuotientGroup.mk' P f := by
      rw [map_mul, map_mul, map_inv, haD _ hfD]
      group
    have h := hinjQ _ haQf f hfQ himg
    calc a * f = (a * f * a⁻¹) * a := by group
      _ = f * a := by rw [h]
  set B₁ : Subgroup Y := Bm.map (MulAut.conj x₀).toMonoidHom with hB₁def
  have hB₁P : B₁ ⊓ P = ⊥ := by
    apply eq_bot_iff.2
    rintro y ⟨hyB, hyP⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hyB
    have hbP : b ∈ P := by
      have h := Subgroup.Normal.conj_mem inferInstance _ hyP x₀⁻¹
      rw [hconj_apply, inv_inv] at h
      have e : x₀⁻¹ * (x₀ * b * x₀⁻¹) * x₀ = b := by group
      rw [e] at h
      exact h
    have hb1 : b ∈ Bm ⊓ P := ⟨hb, hbP⟩
    rw [hBmP, Subgroup.mem_bot] at hb1
    rw [hb1, map_one, Subgroup.mem_bot]
  have hB₁ea : IsElemAbelian p B₁ :=
    CFSG.SectionRank.isElemAbelian_map hBm (MulAut.conj x₀).toMonoidHom
  set B' : Subgroup Y := B₁ ⊓ W with hB'def
  have hB'P : B' ⊓ P = ⊥ := by
    apply eq_bot_iff.2
    have h := inf_le_inf_right P (inf_le_left : B' ≤ B₁)
    rw [hB₁P] at h
    exact h
  have hB'map : B'.map (QuotientGroup.mk' P) = D := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hy).2
    · intro d hd
      obtain ⟨b, hb, hdb⟩ := hDB d hd
      refine Subgroup.mem_map.2 ⟨x₀ * b * x₀⁻¹, Subgroup.mem_inf.2 ⟨?_, ?_⟩, hdb.symm⟩
      · exact Subgroup.mem_map.2 ⟨b, hb, rfl⟩
      · exact Subgroup.mem_comap.2 (by rw [← hdb]; exact hd)
  have hB'card : Nat.card B' = Nat.card D := by
    rw [← card_map_eq_of_inf_bot P hB'P, hB'map]
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p)).1 hDp
  have hWcard : Nat.card W = p ^ j * Nat.card P := by
    rw [hWdef, card_comap_quot, hj]
  have hFW : F ≤ W := inf_le_right
  have hB'W : B' ≤ W := inf_le_right
  have hFWcard : Nat.card (F.subgroupOf W) = p ^ (Nat.card W).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFW).toEquiv, hFD, hj, hWcard,
      fact_pow_mul hP (Nat.card_pos.ne')]
  have hB'Wcard : Nat.card (B'.subgroupOf W) = p ^ (Nat.card W).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'W).toEquiv, hB'card, hj, hWcard,
      fact_pow_mul hP (Nat.card_pos.ne')]
  let SF : Sylow p ↥W := Sylow.ofCard (F.subgroupOf W) hFWcard
  let SB : Sylow p ↥W := Sylow.ofCard (B'.subgroupOf W) hB'Wcard
  have hSF : (SF : Subgroup ↥W) = F.subgroupOf W := rfl
  have hSB : (SB : Subgroup ↥W) = B'.subgroupOf W := rfl
  have hmem : SF ∈ MulAction.orbit ↥W SB := by
    rw [Sylow.orbit_eq_top]
    trivial
  obtain ⟨g, hg⟩ := hmem
  have hg' : g • SB = SF := hg
  have hs : MulAut.conj g • (B'.subgroupOf W) = F.subgroupOf W := by
    rw [← hSB, ← Sylow.coe_subgroup_smul, hg', hSF]
  refine ⟨(g : Y) * x₀, F, hFea, hFD, ?_, hcent⟩
  intro f hf
  have hfW : f ∈ W := (Subgroup.mem_inf.1 hf).2
  have h1 : (⟨f, hfW⟩ : ↥W) ∈ F.subgroupOf W := Subgroup.mem_subgroupOf.2 hf
  rw [← hs] at h1
  obtain ⟨s, hs', hsf⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 h1
  have hsB' : (s : Y) ∈ B' := Subgroup.mem_subgroupOf.1 hs'
  obtain ⟨b, hb, hbs⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hsB').1
  refine ⟨b, hb, ?_⟩
  have hfval : f = (g : Y) * (s : Y) * (g : Y)⁻¹ := by
    have h := congrArg Subtype.val hsf
    simpa [MulAut.conj_apply] using h.symm
  rw [hfval, ← hbs, hconj_apply]
  group

end LiftMain


section MUtil

theorem mem_normalizer_of_conj_le {X : Type} [Group X] {K : Subgroup X} {g : X}
    (h : ∀ x ∈ K, g * x * g⁻¹ ∈ K) (h' : ∀ x ∈ K, g⁻¹ * x * g⁻¹⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    have := h' _ hx
    simpa [mul_assoc] using this

theorem map_conj_self {X : Type} [Group X] {M : Subgroup X} {g : X} (hg : g ∈ M) :
    M.map (MulAut.conj g).toMonoidHom = M := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hg hx) (M.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g, M.mul_mem (M.mul_mem (M.inv_mem hg) hx) hg, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem lemma118R_elemAb_subgroupOf {G : Type} [Group G] [Finite G] {p : ℕ} {B M : Subgroup G}
    (hB : IsElemAbelian p B) : IsElemAbelian p (B.subgroupOf M) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
  · exact comm_of_elemAb hB (Subgroup.mem_subgroupOf.1 x.2) (Subgroup.mem_subgroupOf.1 y.2)
  · apply Subtype.ext
    simpa using hB.2 _ (Subgroup.mem_subgroupOf.1 hx)

theorem eq_one_of_pow_eq_one_of_not_dvd {X : Type} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    {N : Subgroup X} (hN : ¬ p ∣ Nat.card N) {x : X} (hxN : x ∈ N) (hx : x ^ p = 1) : x = 1 := by
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  rcases (Nat.dvd_prime hp.out).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at h2
    exact absurd h2 hN

theorem pRank_le_twoLocalPrimeRank {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {H : Subgroup G} (hH : IsTwoLocal H) :
    CFSG.Open.pRank p H ≤ CFSG.Open.twoLocalPrimeRank p G := by
  have hbdd : BddAbove {k | ∃ K : Subgroup G, IsTwoLocal K ∧ CFSG.Open.pRank p K = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨K, -, rfl⟩
    refine CFSG.SectionRank.pRank_le hp.out.one_lt (k := Nat.card G) (fun E _ hE => ?_)
    exact (Subgroup.card_le_card_group E).trans (Nat.lt_pow_self hp.out.one_lt).le
  exact le_csSup hbdd ⟨H, hH, rfl⟩

theorem normalizer_map_le {G : Type} [Group G] {M : Subgroup G} {P : Subgroup M} :
    (Subgroup.normalizer (P : Set M)).map M.subtype ≤
      Subgroup.normalizer ((P.map M.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := Subgroup.mem_normalizer_iff.1 hx
  have hx'' := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem (Subgroup.normalizer (P : Set M)) hx)
  apply mem_normalizer_of_conj_le
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨x * z * x⁻¹, (hx' z).1 hz, by simp⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨x⁻¹ * z * x⁻¹⁻¹, (hx'' z).1 hz, by simp⟩

theorem twoLocalPrimeRank_subgroup_le {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (M : Subgroup G) :
    CFSG.Open.twoLocalPrimeRank p ↥M ≤ CFSG.Open.twoLocalPrimeRank p G := by
  unfold CFSG.Open.twoLocalPrimeRank
  apply csSup_le'
  rintro k ⟨H', hH', rfl⟩
  obtain ⟨P, hP1, hP2, hPH⟩ := hH'
  have hP'bot : P.map M.subtype ≠ ⊥ := by
    intro h
    apply hP1
    rw [eq_bot_iff]
    intro z hz
    have hzmem : (z : G) ∈ P.map M.subtype := ⟨z, hz, rfl⟩
    rw [h, Subgroup.mem_bot] at hzmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext hzmem
  have hP'2 : IsPGroup 2 ((P.map M.subtype : Subgroup G)) := IsPGroup.map hP2 M.subtype
  have hT : IsTwoLocal (Subgroup.normalizer ((P.map M.subtype : Subgroup G) : Set G)) :=
    ⟨P.map M.subtype, hP'bot, hP'2, rfl⟩
  calc CFSG.Open.pRank p H' ≤ CFSG.Open.pRank p (H'.map M.subtype) :=
        CFSG.SectionRank.pRank_le_map hp.out.one_lt M.subtype Subtype.val_injective H'
    _ ≤ CFSG.Open.pRank p (Subgroup.normalizer ((P.map M.subtype : Subgroup G) : Set G)) := by
        rw [hPH]
        exact CFSG.SectionRank.pRank_mono hp.out.one_lt normalizer_map_le
    _ ≤ CFSG.Open.twoLocalPrimeRank p G := pRank_le_twoLocalPrimeRank hT

end MUtil


section QuotBar

variable {G : Type} [Group G] [Finite G]

theorem barX_map_conj (p : ℕ) (M L : Subgroup G) {g : G} (hg : g ∈ M) :
    barX p M (L.map (MulAut.conj g).toMonoidHom) =
      (barX p M L).map
        (MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩)).toMonoidHom := by
  classical
  unfold barX
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
    have hlM : l ∈ M := by
      have e : l = g⁻¹ * (y : G) * g⁻¹⁻¹ := by
        have hlg' : g * l * g⁻¹ = (y : G) := by
          rw [← hlg]; rfl
        rw [← hlg']; group
      rw [e]
      exact M.mul_mem (M.mul_mem (M.inv_mem hg) y.2) (M.inv_mem (M.inv_mem hg))
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨l, hlM⟩,
      Subgroup.mem_map.2 ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩, ?_⟩
    show QuotientGroup.mk' _ (⟨g, hg⟩ * ⟨l, hlM⟩ * ⟨g, hg⟩⁻¹) = QuotientGroup.mk' _ y
    congr 1
    apply Subtype.ext
    show g * l * g⁻¹ = (y : G)
    rw [← hlg]
    rfl
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · exact Subgroup.mem_map.2 ⟨(w : G), Subgroup.mem_subgroupOf.1 hw, by
        simp [MulAut.conj_apply]⟩
    · simp [MulAut.conj_apply, map_mul, map_inv]

theorem mk_mem_normalizer_barX (p : ℕ) (M L : Subgroup G) {g : G} (hg : g ∈ M)
    (h1 : ∀ l ∈ L, g * l * g⁻¹ ∈ L) (h2 : ∀ l ∈ L, g⁻¹ * l * g⁻¹⁻¹ ∈ L) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩ ∈
      Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  apply mem_normalizer_of_conj_le
  · intro x hx
    have hx' : x ∈ barX p M L := hx
    unfold barX at hx' ⊢
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hx'
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩ * u' * ⟨g, hg⟩⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · exact h1 _ (Subgroup.mem_subgroupOf.1 hu')
    · simp [map_mul, map_inv]
  · intro x hx
    have hx' : x ∈ barX p M L := hx
    unfold barX at hx' ⊢
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hx'
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩⁻¹ * u' * ⟨g, hg⟩⁻¹⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · exact h2 _ (Subgroup.mem_subgroupOf.1 hu')
    · simp [map_mul, map_inv]

theorem comm_of_comm_eq_one {Z : Type} [Group Z] {a b : Z} (h : a * b * a⁻¹ * b⁻¹ = 1) :
    a * b = b * a := by
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h, one_mul]

theorem barX_comm_of_commutator (p : ℕ) (M L L' : Subgroup G)
    (hc : ⁅L, L'⁆ ≤ GLAPPrimeCoreOf p M) :
    ∀ x ∈ barX p M L, ∀ y ∈ barX p M L', x * y = y * x := by
  intro x hx y hy
  unfold barX at hx hy
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
  have hcG : (u : G) * (v : G) * (u : G)⁻¹ * (v : G)⁻¹ ∈ GLAPPrimeCoreOf p M := by
    apply hc
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hu)
      (Subgroup.mem_subgroupOf.1 hv)
  obtain ⟨hcM, hcN⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff
    p M _).1 hcG
  have hpi : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (u * v * u⁻¹ * v⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hcN
  apply comm_of_comm_eq_one
  simpa [map_mul, map_inv] using hpi

end QuotBar


theorem succ_add_two_le_three_pow : ∀ t : ℕ, 1 ≤ t → t + 2 ≤ 3 ^ t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem pow_pred_le_div {p r n : ℕ} (hp3 : 3 ≤ p) (hr2 : 2 ≤ r) (hrn : p ^ r < n) :
    r + 1 ≤ n / p := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  have ht2 : t + 2 ≤ 3 ^ t := succ_add_two_le_three_pow t (by omega)
  have ht3 : 3 ^ t ≤ p ^ t := Nat.pow_le_pow_left hp3 t
  have hdiv : p ^ t ≤ n / p :=
    (Nat.le_div_iff_mul_le (by omega)).2 (by rw [← pow_succ]; exact hrn.le)
  omega

end Lemma118R

open Lemma118R

theorem lemma118Return_of_inputs (hR2 : Lemma118R.Input11_2Alt) (hAut : Lemma118R.InputAutAltOdd)
    (hRank : Lemma118R.Input10_6AltRank) (hMax : Lemma118R.Input10_5AltMax) :
    Lemma118Return := by
  intro G _ _ m p B M E A h hbig a haM hap
  obtain ⟨L, n, hL, hLalt, hrn⟩ := hbig
  have hstd : GLStanding G m p := h.standing
  haveI hpf : Fact p.Prime := ⟨hstd.prime⟩
  have hp2 : p ≠ 2 := hstd.ne_two
  have hp3 : 3 ≤ p := by have := hpf.out.two_le; omega
  have hr2 : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := h.pair.1.2.2
  have hpr9 : 9 ≤ p ^ CFSG.Open.pRank p (E ⊓ A) := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank p (E ⊓ A) := Nat.pow_le_pow_right (by norm_num) hr2
      _ ≤ p ^ CFSG.Open.pRank p (E ⊓ A) := Nat.pow_le_pow_left hp3 _
  have hn10 : 10 ≤ n := by omega
  have hrn1 : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ n / p := pow_pred_le_div hp3 hr2 hrn
  have hBM : B ≤ M := CFSG.LocalAnalysis.GLTheoremB.le_of_isPreUniquenessTwoLocal hstd h.bOne h.pre
  obtain ⟨hBel, hBcard', -⟩ := h.bOne.1
  have hBcard : Nat.card B = p ^ m := by rw [hBcard', hstd.rank_eq]
  have hMtl : IsTwoLocal M := h.pre.1.1
  have hMne : M ≠ ⊤ := CFSG.LocalAnalysis.GLTheoremB.isTwoLocal_ne_top hstd hMtl
  have hpB : CFSG.Open.pRank p B = m :=
    CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card hpf.out hBel hBcard
  have hrankM : CFSG.Open.twoLocalPrimeRank p ↥M ≤ CFSG.Open.pRank p B := by
    rw [hpB]
    calc CFSG.Open.twoLocalPrimeRank p ↥M ≤ CFSG.Open.twoLocalPrimeRank p G :=
          twoLocalPrimeRank_subgroup_le M
      _ = m := by rw [← hstd.rank_eq]; rfl
  have hNn : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥M) :=
    (Nat.Prime.coprime_iff_not_dvd hpf.out).1
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥M)
  have hLsub : IsSubnormal L M := hL.2.1
  obtain ⟨Bm, hBmdef⟩ : ∃ Bm : Subgroup ↥M, Bm = B.subgroupOf M := ⟨_, rfl⟩
  have hBmel : IsElemAbelian p Bm := by rw [hBmdef]; exact lemma118R_elemAb_subgroupOf hBel
  have hBmcard : Nat.card Bm = p ^ m := by
    rw [hBmdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv, hBcard]
  have hBmN : Bm ⊓ GLAPPrimeCore p ↥M = ⊥ := by
    apply eq_bot_iff.2
    intro x hx
    have hx1 := eq_one_of_pow_eq_one_of_not_dvd hNn hx.2 (hBmel.2 x hx.1)
    rw [hx1]
    exact Subgroup.one_mem _
  obtain ⟨ã, hãdef⟩ : ∃ ã : ↥M ⧸ GLAPPrimeCore p ↥M, ã = QuotientGroup.mk' (GLAPPrimeCore p ↥M)
      ⟨a, haM⟩ := ⟨_, rfl⟩
  have hã : ã ^ p = 1 := by
    rw [hãdef, ← map_pow]
    have : (⟨a, haM⟩ : ↥M) ^ p = 1 := Subtype.ext hap
    rw [this, map_one]
  have hB₀ea : IsElemAbelian p (Bm.map (QuotientGroup.mk' (GLAPPrimeCore p ↥M))) :=
    CFSG.SectionRank.isElemAbelian_map hBmel _
  have hB₀card : Nat.card (Bm.map (QuotientGroup.mk' (GLAPPrimeCore p ↥M))) = p ^ m := by
    rw [card_map_eq_of_inf_bot _ hBmN, hBmcard]
  have hHm : CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) ≤ m := by
    rw [CFSG.SectionRank.pRank_quotient_eq _ hNn]
    have hMtop : (⊤ : Subgroup ↥M).map M.subtype = M := by
      ext x
      simp
    calc CFSG.Open.pRank p (⊤ : Subgroup ↥M)
        ≤ CFSG.Open.pRank p ((⊤ : Subgroup ↥M).map M.subtype) :=
          CFSG.SectionRank.pRank_le_map hpf.out.one_lt M.subtype Subtype.val_injective _
      _ = CFSG.Open.pRank p M := by rw [hMtop]
      _ ≤ CFSG.Open.twoLocalPrimeRank p G := pRank_le_twoLocalPrimeRank hMtl
      _ = m := by rw [← hstd.rank_eq]; rfl
  obtain ⟨Lj, hLjdef⟩ : ∃ Lj : ℕ → Subgroup G, Lj = fun j => L.map (MulAut.conj (a ^ j)).toMonoidHom :=
    ⟨_, rfl⟩
  have hLjapp : ∀ j, Lj j = L.map (MulAut.conj (a ^ j)).toMonoidHom := fun j => by
    rw [hLjdef]
  have haj : ∀ j : ℕ, a ^ j ∈ M := fun j => M.pow_mem haM j
  have hLj_comp : ∀ j, GLAPComponent p M (Lj j) := by
    intro j
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL (a ^ j)⁻¹
    unfold GLBConj at h1
    rw [inv_inv, map_conj_self (haj j)] at h1
    rw [hLjapp j]
    exact h1
  obtain ⟨Ĩ, hĨdef⟩ : ∃ Ĩ : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M), Ĩ = barX p M L := ⟨_, rfl⟩
  have hĨalt : IsAltType n ↥Ĩ := by
    rw [hĨdef]
    obtain ⟨eL⟩ := hLalt
    exact ⟨(CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barXEquiv hpf.out hLsub).symm.trans eL⟩
  have hpowel : ∀ j : ℕ, ã ^ j = QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨a ^ j, haj j⟩ := by
    intro j
    rw [hãdef, ← map_pow]
    congr 1
  have hIc : ∀ j, barX p M (Lj j) = Icof ã Ĩ j := by
    intro j
    rw [hLjapp j, barX_map_conj p M L (haj j), hĨdef]
    unfold Icof cj
    rw [hpowel j]
  have hLj_alt : ∀ j, IsAltType n (barOf p (Lj j)) := by
    intro j
    obtain ⟨eA⟩ := (isAltType_cj (ã ^ j) hĨalt)
    exact ⟨(CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barXEquiv hpf.out
      (hLj_comp j).2.1).trans ((MulEquiv.subgroupCongr (hIc j)).trans eA)⟩
  have hLj_norm : ∀ j, B ≤ Subgroup.normalizer ((Lj j : Subgroup G) : Set G) := fun j =>
    hR2 G m p hstd M B (Lj j) hMne hBel hBM hrankM (hLj_comp j) n hn10 (hLj_alt j)
  have hnorm : ∀ j : ℕ, (Bm.map (QuotientGroup.mk' (GLAPPrimeCore p ↥M))) ≤
      Subgroup.normalizer ((Icof ã Ĩ j : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set _) := by
    intro j d hd
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hd
    have hb' : b ∈ B.subgroupOf M := by rw [← hBmdef]; exact hb
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.1 hb'
    have hbN := hLj_norm j hbB
    have hn1 := Subgroup.mem_normalizer_iff.1 hbN
    have hn2 := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbN)
    rw [← hIc j]
    have hmem := mk_mem_normalizer_barX p M (Lj j) b.2 (fun l hl => (hn1 l).1 hl)
      (fun l hl => (hn2 l).1 hl)
    exact hmem
  have hcomm : ∀ i j : ℕ, Icof ã Ĩ i ≠ Icof ã Ĩ j →
      ∀ x ∈ Icof ã Ĩ i, ∀ y ∈ Icof ã Ĩ j, x * y = y * x := by
    intro i j hne x hx y hy
    have hLne : Lj i ≠ Lj j := by
      intro heq
      apply hne
      rw [← hIc i, ← hIc j, heq]
    have hc := CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne
      hpf.out (hLj_comp i) (hLj_comp j) hLne
    rw [← hIc i] at hx
    rw [← hIc j] at hy
    exact barX_comm_of_commutator p M (Lj i) (Lj j) hc x hx y hy
  obtain ⟨h₀, D, hDea, hDcard, hDsub, hDcent⟩ :=
    core_exists hp2 hn10 hAut hRank hMax hHm hB₀ea hB₀card hã hĨalt hnorm hcomm
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥M) h₀
  have hDB : ∀ d ∈ D, ∃ b ∈ Bm, d = QuotientGroup.mk' (GLAPPrimeCore p ↥M) (x₀ * b * x₀⁻¹) := by
    intro d hd
    obtain ⟨β, hβ, hβd⟩ := Subgroup.mem_map.1 (hDsub d hd)
    obtain ⟨b, hb, hbβ⟩ := Subgroup.mem_map.1 hβ
    refine ⟨b, hb, ?_⟩
    rw [← hβd, ← hbβ, ← hx₀]
    simp [MulAut.conj_apply, map_mul, map_inv]
  have haD : ∀ d ∈ D, QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨a, haM⟩ : ↥M) * d =
      d * QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨a, haM⟩ : ↥M) := by
    intro d hd
    rw [← hãdef]
    exact hDcent d hd
  have ha' : (⟨a, haM⟩ : ↥M) ^ p = 1 := Subtype.ext hap
  obtain ⟨x, F, hFea, hFcard, hFsub, hFcent⟩ :=
    lift_elemAb (GLAPPrimeCore p ↥M) hNn hBmel hBmN ha' hDea haD hDB
  have hFGea : IsElemAbelian p (F.map M.subtype) := CFSG.SectionRank.isElemAbelian_map hFea _
  have hFGcard : Nat.card (F.map M.subtype) = p ^ (n / p) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hFcard, hDcard]
  have hxM : ((x : G))⁻¹ ∈ M := M.inv_mem x.2
  have hF₁ : F.map M.subtype ≤ GLBConj ((x : G))⁻¹ B := by
    rintro g ⟨f, hf, rfl⟩
    obtain ⟨b, hb, hfb⟩ := hFsub f hf
    unfold GLBConj
    have hb' : b ∈ B.subgroupOf M := by rw [← hBmdef]; exact hb
    refine Subgroup.mem_map.2 ⟨(b : G), Subgroup.mem_subgroupOf.1 hb', ?_⟩
    rw [inv_inv]
    have hfG : (f : G) = (x : G) * (b : G) * (x : G)⁻¹ := by
      rw [hfb]; rfl
    show (MulAut.conj (x : G)).toMonoidHom (b : G) = (f : G)
    rw [hfG]
    rfl
  have hcentG : ∀ g ∈ F.map M.subtype, a * g = g * a := by
    rintro g ⟨f, hf, rfl⟩
    have := congrArg Subtype.val (hFcent f hf)
    simpa using this
  have hc : Subgroup.zpowers a ≤ Subgroup.centralizer ((F.map M.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro g hg
    exact (hcentG g hg).symm
  have hr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p (F.map M.subtype) := by
    have h1 := CFSG.SectionRank.le_pRank hpf.out.one_lt (le_refl (F.map M.subtype)) hFGea hFGcard
    omega
  exact exists_inD_of_centralizes_conj h hxM hF₁ hFGea hr hap hc

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
