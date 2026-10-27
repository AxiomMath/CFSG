module

public import CFSG.ClassicalInvolution.RouteD.TypeUThreeChart
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagUnitary
public import CFSG.ClassicalInvolution.RouteD.TypeUPatternModel

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg

section GU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

@[expose] noncomputable def signGU (v : Fin n → ZMod 2) : GUid (unitaryInvolution K p f) n :=
  ⟨diagGL fun i => ((signN (v i) : normOne (unitaryInvolution K p f)) : Kˣ), by
    rw [mem_GUid, coe_diagGL]
    exact conjTr_diagonal_mul_self (fun i => (signN (v i) : normOne (unitaryInvolution K p f)))⟩

theorem coe_signGU (v : Fin n → ZMod 2) :
    ((signGU (K := K) (p := p) (f := f) v : GUid (unitaryInvolution K p f) n) :
      GL (Fin n) K) = diagGL fun i => ((signN (v i) : normOne (unitaryInvolution K p f)) : Kˣ) :=
  rfl

theorem signGU_mul_self (v : Fin n → ZMod 2) :
    signGU (K := K) (p := p) (f := f) v * signGU v = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_signGU, coe_diagGL, Matrix.diagonal_mul_diagonal,
    Subgroup.coe_one, Units.val_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [coe_signN]
  exact signVal_mul_self (v i)

theorem conjSUid_signGU (hK : Nat.card K = (p ^ f) ^ 2) (v : Fin n → ZMod 2) (y : Su K p f n) :
    conjSUid (unitaryInvolution K p f) n (signGU v) y = conjSign hK v y :=
  rfl

theorem conjSUid_suToGU_conj (x₀ : GUid (unitaryInvolution K p f) n) (g y : Su K p f n) :
    conjSUid (unitaryInvolution K p f) n
        (suToGU (unitaryInvolution K p f) n g * x₀ * (suToGU (unitaryInvolution K p f) n g)⁻¹)
        y =
      g * conjSUid (unitaryInvolution K p f) n x₀ (g⁻¹ * y * g) * g⁻¹ := by
  apply Subtype.ext
  simp only [coe_conjSUid, Subgroup.coe_mul, Subgroup.coe_inv, coe_suToGU]
  group

end GU

section Dich

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_dichotomy (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {H : Type} [Group H] (θ : Su K p f (3 + 1) →* H)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (3 + 1)))
    {R : Subgroup (Su K p f (3 + 1))}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 3 + 1 by norm_num)) {v : H}
    (hv : v ∈ Subgroup.normalizer (θ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * θ r = θ r * v) :
    (∃ R'' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 3 + 1 by norm_num),
        (∀ r ∈ R, ∀ s ∈ R'', r * s = s * r) ∧ ∀ s ∈ R'', v * θ s = θ s * v) ∨
      ∃ Y₀ : GUid (unitaryInvolution K p f) (3 + 1), Y₀ * Y₀ = 1 ∧
        (∀ r ∈ R, (Y₀ : GL (Fin (3 + 1)) K) * (r : GL (Fin (3 + 1)) K) =
          (r : GL (Fin (3 + 1)) K) * Y₀) ∧
        ∀ y : Su K p f (3 + 1),
          v * θ y * v⁻¹ = θ (conjSUid (unitaryInvolution K p f) (3 + 1) Y₀ y) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hn : 2 ≤ 3 + 1 := by norm_num
  set S₂ : Subgroup (Su K p f (3 + 1)) := (blockEmb2 K p f 3 ⟨2, by omega⟩).range with hS₂
  set S₀ : Subgroup (Su K p f (3 + 1)) := (blockEmb2 K p f 3 ⟨0, by omega⟩).range with hS₀
  have hS₂mem : S₂ ∈ longRootSetU (K := K) (p := p) (f := f) hn := by
    rw [hS₂, range_blockEmb2_eq_LcU_nodePair h2 (m := 3) (a := 2) (by omega)]
    exact LcU_mem_longRootSetU h2 hn _
  have hS₀mem : S₀ ∈ longRootSetU (K := K) (p := p) (f := f) hn := by
    rw [hS₀, range_blockEmb2_eq_LcU_nodePair h2 (m := 3) (a := 0) (by omega)]
    exact LcU_mem_longRootSetU h2 hn _
  obtain ⟨g₀, hg₀⟩ := (mem_longRootSetU_iff hn).mp hR
  obtain ⟨P₀, hP₀⟩ := (mem_longRootSetU_iff hn).mp hS₂mem
  set g : Su K p f (3 + 1) := g₀ * P₀⁻¹ with hg
  have hRg : R = S₂.map (MulAut.conj g).toMonoidHom := by
    rw [hg₀, hP₀, Subgroup.map_map]
    congr 1
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
    group
  obtain ⟨i₀, hi₀⟩ := hS₀mem
  have hR''mem : S₀.map (MulAut.conj g).toMonoidHom ∈
      longRootSetU (K := K) (p := p) (f := f) hn := ⟨g * i₀ * g⁻¹, hi₀.conj g⟩
  clear_value g
  have hψg : θ g ∈ θ.range := ⟨g, rfl⟩
  set w : H := (θ g)⁻¹ * v * θ g with hwdef
  have hw : w ∈ Subgroup.normalizer (θ.range : Set H) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hψg)) hv)
      (Subgroup.le_normalizer hψg)
  have hw2 : w * w = 1 := by
    calc w * w = (θ g)⁻¹ * (v * v) * θ g := by rw [hwdef]; group
      _ = 1 := by rw [hv2]; group
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwS : ∀ r ∈ S₂, w * θ r = θ r * w := by
    intro r hr
    have hmem : g * r * g⁻¹ ∈ R := by rw [hRg]; exact ⟨r, hr, rfl⟩
    have h := hvR _ hmem
    rw [map_mul, map_mul, map_inv] at h
    calc w * θ r = (θ g)⁻¹ * (v * (θ g * θ r * (θ g)⁻¹)) * θ g := by rw [hwdef]; group
      _ = (θ g)⁻¹ * ((θ g * θ r * (θ g)⁻¹) * v) * θ g := by rw [h]
      _ = θ r * w := by rw [hwdef]; group
  let σ : H ≃* H := MulAut.conj w
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    show w * (w * y * w⁻¹) * w⁻¹ = y
    rw [hwinv]
    calc w * (w * y * w) * w = (w * w) * y * (w * w) := by group
      _ = y := by rw [hw2]; group
  have hstab : ∀ x, σ (θ x) ∈ θ.range := fun x =>
    (Subgroup.mem_normalizer_iff.mp hw (θ x)).mp ⟨x, rfl⟩
  have hfix : ∀ A : Su K p f 2, σ (θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A)) =
      θ (blockEmb2 K p f 3 ⟨2, by omega⟩ A) := by
    intro A
    show w * θ _ * w⁻¹ = θ _
    rw [hwS _ ⟨A, rfl⟩]
    group
  by_cases hmove : ∃ A : Su K p f 2, σ (θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)) ≠
      θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)
  · right
    obtain ⟨h, -, hcent, hact⟩ :=
      unitary_partner_chart_three hK hp2 hq θ hker σ hσ hstab hfix hmove
    set pd : GUid (unitaryInvolution K p f) (3 + 1) := signGU (partnerSigns 3 0) with hpd
    set Y₁ : GUid (unitaryInvolution K p f) (3 + 1) :=
      suToGU _ _ h * pd * (suToGU _ _ h)⁻¹ with hY₁
    have hY₁sq : Y₁ * Y₁ = 1 := by
      calc Y₁ * Y₁ = suToGU _ _ h * (pd * pd) * (suToGU _ _ h)⁻¹ := by rw [hY₁]; group
        _ = 1 := by rw [hpd, signGU_mul_self]; group
    have hact' : ∀ y, σ (θ y) = θ (conjSUid (unitaryInvolution K p f) (3 + 1) Y₁ y) := by
      intro y
      have h1 := hact (h⁻¹ * y * h)
      rw [show h * (h⁻¹ * y * h) * h⁻¹ = y by group] at h1
      rw [h1]
      congr 1
      rw [hY₁, conjSUid_suToGU_conj, hpd, conjSUid_signGU hK]
    have hcomY : ∀ A : Su K p f 2,
        (Y₁ : GL (Fin (3 + 1)) K) *
            ((blockEmb2 K p f 3 ⟨2, by omega⟩ A : Su K p f (3 + 1)) : GL (Fin (3 + 1)) K) =
          ((blockEmb2 K p f 3 ⟨2, by omega⟩ A : Su K p f (3 + 1)) : GL (Fin (3 + 1)) K) *
            (Y₁ : GL (Fin (3 + 1)) K) := by
      intro A
      set T : GL (Fin (3 + 1)) K :=
        ((blockEmb2 K p f 3 ⟨2, by omega⟩ A : Su K p f (3 + 1)) : GL (Fin (3 + 1)) K) with hT
      have e1 : (h : GL (Fin (3 + 1)) K) * T * (h : GL (Fin (3 + 1)) K)⁻¹ = T :=
        congrArg (fun x : Su K p f (3 + 1) => (x : GL (Fin (3 + 1)) K)) (hcent A)
      have hmemA : blockEmb2 K p f 3 ⟨2, by omega⟩ A ∈
          LcU K p f (nodePair 3 2 (by omega)) := by
        rw [← range_blockEmb2_eq_LcU_nodePair h2 (m := 3) (a := 2) (by omega)]
        exact ⟨A, rfl⟩
      have e2' := conjSign_eq_of_const hK h2 (partnerSigns 3 0) (T := nodePair 3 2 (by omega))
        (by
          intro a ha b hb
          simp only [nodePair, natPair, Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [partnerSigns])
        hmemA
      have e2 : (pd : GL (Fin (3 + 1)) K) * T * (pd : GL (Fin (3 + 1)) K)⁻¹ = T :=
        congrArg (fun x : Su K p f (3 + 1) => (x : GL (Fin (3 + 1)) K)) e2'
      have c1 : Commute (h : GL (Fin (3 + 1)) K) T := mul_inv_eq_iff_eq_mul.mp e1
      have c2 : Commute (pd : GL (Fin (3 + 1)) K) T := mul_inv_eq_iff_eq_mul.mp e2
      exact ((c1.mul_left c2).mul_left c1.inv_left).eq
    set G : GUid (unitaryInvolution K p f) (3 + 1) := suToGU _ _ g with hG
    refine ⟨G * Y₁ * G⁻¹, ?_, ?_, ?_⟩
    · calc G * Y₁ * G⁻¹ * (G * Y₁ * G⁻¹) = G * (Y₁ * Y₁) * G⁻¹ := by group
        _ = 1 := by rw [hY₁sq]; group
    · intro r hr
      rw [hRg] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      obtain ⟨A, rfl⟩ := ha
      have e : (((MulAut.conj g).toMonoidHom (blockEmb2 K p f 3 ⟨2, by omega⟩ A) :
          Su K p f (3 + 1)) : GL (Fin (3 + 1)) K) =
          (G : GL (Fin (3 + 1)) K) *
            ((blockEmb2 K p f 3 ⟨2, by omega⟩ A : Su K p f (3 + 1)) : GL (Fin (3 + 1)) K) *
              (G : GL (Fin (3 + 1)) K)⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
          Subgroup.coe_inv, hG, coe_suToGU]
      rw [e]
      calc ((G * Y₁ * G⁻¹ : GUid (unitaryInvolution K p f) (3 + 1)) : GL (Fin (3 + 1)) K) *
            ((G : GL (Fin (3 + 1)) K) *
              ((blockEmb2 K p f 3 ⟨2, by omega⟩ A : Su K p f (3 + 1)) : GL (Fin (3 + 1)) K) *
                (G : GL (Fin (3 + 1)) K)⁻¹)
          = (G : GL (Fin (3 + 1)) K) * ((Y₁ : GL (Fin (3 + 1)) K) *
              ((blockEmb2 K p f 3 ⟨2, by omega⟩ A : Su K p f (3 + 1)) : GL (Fin (3 + 1)) K)) *
                (G : GL (Fin (3 + 1)) K)⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
        _ = (G : GL (Fin (3 + 1)) K) * (((blockEmb2 K p f 3 ⟨2, by omega⟩ A : Su K p f (3 + 1)) :
              GL (Fin (3 + 1)) K) * (Y₁ : GL (Fin (3 + 1)) K)) *
                (G : GL (Fin (3 + 1)) K)⁻¹ := by rw [hcomY A]
        _ = _ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            group
    · intro y
      rw [hG, conjSUid_suToGU_conj]
      have h1 : v * θ y * v⁻¹ = θ g * (w * θ (g⁻¹ * y * g) * w⁻¹) * (θ g)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hwdef]
        group
      have h2' : w * θ (g⁻¹ * y * g) * w⁻¹ = σ (θ (g⁻¹ * y * g)) := rfl
      rw [h1, h2', hact', ← map_mul, ← map_inv, ← map_mul]
  · left
    push Not at hmove
    have hwS₀ : ∀ r ∈ S₀, w * θ r = θ r * w := by
      rintro r ⟨A, rfl⟩
      have e : w * θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A) * w⁻¹ =
          θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A) := hmove A
      calc w * θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A)
          = w * θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A) * w⁻¹ * w := by group
        _ = θ (blockEmb2 K p f 3 ⟨0, by omega⟩ A) * w := by rw [e]
    refine ⟨S₀.map (MulAut.conj g).toMonoidHom, hR''mem, ?_, ?_⟩
    · rintro r hr _ ⟨b, hb, rfl⟩
      rw [hRg] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      obtain ⟨A, rfl⟩ := ha
      obtain ⟨B, rfl⟩ := hb
      have hc := blockEmb2_comm (K := K) (p := p) (f := f) 3 ⟨0, by omega⟩ ⟨2, by omega⟩
        (by simp) B A
      show g * blockEmb2 K p f 3 ⟨2, by omega⟩ A * g⁻¹ *
          (g * blockEmb2 K p f 3 ⟨0, by omega⟩ B * g⁻¹) =
        g * blockEmb2 K p f 3 ⟨0, by omega⟩ B * g⁻¹ *
          (g * blockEmb2 K p f 3 ⟨2, by omega⟩ A * g⁻¹)
      calc g * blockEmb2 K p f 3 ⟨2, by omega⟩ A * g⁻¹ *
            (g * blockEmb2 K p f 3 ⟨0, by omega⟩ B * g⁻¹)
          = g * (blockEmb2 K p f 3 ⟨2, by omega⟩ A * blockEmb2 K p f 3 ⟨0, by omega⟩ B) * g⁻¹ := by
            group
        _ = g * (blockEmb2 K p f 3 ⟨0, by omega⟩ B * blockEmb2 K p f 3 ⟨2, by omega⟩ A) * g⁻¹ := by
            rw [hc]
        _ = _ := by group
    · rintro _ ⟨b, hb, rfl⟩
      have h1 := hwS₀ b hb
      show v * θ (g * b * g⁻¹) = θ (g * b * g⁻¹) * v
      rw [map_mul, map_mul, map_inv]
      calc v * (θ g * θ b * (θ g)⁻¹) = θ g * (w * θ b) * (θ g)⁻¹ := by rw [hwdef]; group
        _ = θ g * (θ b * w) * (θ g)⁻¹ := by rw [h1]
        _ = (θ g * θ b * (θ g)⁻¹) * v := by rw [hwdef]; group

end Dich

end CFSG.ClassicalInvolution.Asc77
