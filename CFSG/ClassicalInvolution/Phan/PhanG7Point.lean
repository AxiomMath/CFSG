module

public import CFSG.ClassicalInvolution.Phan.PhanG6Oriented

public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary
open CFSG.Timmesfeld (edgeD)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G}

section Helpers

theorem mem_diagTorus2_iff_commute_zero (hK : Nat.card K = (p ^ f) ^ 2) {θ : Su K p f 3 →* G}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {s : normOne (unitaryInvolution K p f)}
    (hs : (s : Kˣ) ≠ 1) (A : Su K p f 2) :
    A ∈ diagTorus2 K p f ↔
      θ (embSUid (unitaryInvolution K p f) 2 A) *
          θ (embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) s)) =
        θ (embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) s)) *
          θ (embSUid (unitaryInvolution K p f) 2 A) := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg θ (D12_D23_comm (mem_D12_iff.2 ⟨u, rfl⟩) (mem_D23_iff.2 ⟨s, rfl⟩))
  · exact mem_diagTorus2_of_map_commute_zero hK hker hs

theorem mem_diagTorus2_iff_commute_two (hK : Nat.card K = (p ^ f) ^ 2) {θ : Su K p f 3 →* G}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {s : normOne (unitaryInvolution K p f)}
    (hs : (s : Kˣ) ≠ 1) (A : Su K p f 2) :
    A ∈ diagTorus2 K p f ↔
      θ (embSUid (unitaryInvolution K p f) 0 A) *
          θ (embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) s)) =
        θ (embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) s)) *
          θ (embSUid (unitaryInvolution K p f) 0 A) := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg θ (D12_D23_comm (mem_D12_iff.2 ⟨s, rfl⟩) (mem_D23_iff.2 ⟨u, rfl⟩)).symm
  · exact mem_diagTorus2_of_map_commute_two hK hker hs

theorem map_diagTorus2_eq_of_commute {a b : Su K p f 2 →* G} (hr : a.range = b.range) (y : G)
    (ha : ∀ A, A ∈ diagTorus2 K p f ↔ a A * y = y * a A)
    (hb : ∀ A, A ∈ diagTorus2 K p f ↔ b A * y = y * b A) :
    (diagTorus2 K p f).map a = (diagTorus2 K p f).map b := by
  have key : ∀ {a b : Su K p f 2 →* G}, a.range = b.range →
      (∀ A, A ∈ diagTorus2 K p f ↔ a A * y = y * a A) →
      (∀ A, A ∈ diagTorus2 K p f ↔ b A * y = y * b A) →
      (diagTorus2 K p f).map a ≤ (diagTorus2 K p f).map b := by
    intro a b hr ha hb
    rintro _ ⟨A, hA, rfl⟩
    have hmem : a A ∈ b.range := hr ▸ ⟨A, rfl⟩
    obtain ⟨A', hA'⟩ := hmem
    refine ⟨A', (hb A').2 ?_, hA'⟩
    rw [hA']
    exact (ha A).1 hA
  exact le_antisymm (key hr ha hb) (key hr.symm hb ha)

end Helpers

section Mixed

theorem exists_chain_123 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S) :
    ∃ ψ : Su K p f 4 →* G, PhanChain S ![2, 1, 3] ψ := by
  classical
  let u : ℕ → Subgroup G := fun i =>
    if i = 0 then (S.ι 2).range else if i = 1 then (S.ι 1).range else (S.ι 3).range
  let w : ℕ → Subgroup G := fun i => if i = 0 then (S.θ 1).range else (S.θ 2).range
  have hu0 : u 0 = (S.ι 2).range := by simp [u]
  have hu1 : u 1 = (S.ι 1).range := by simp [u]
  have hu2 : u 2 = (S.ι 3).range := by simp [u]
  have hw0 : w 0 = (S.θ 1).range := by simp [w]
  have hw1 : w 1 = (S.θ 2).range := by simp [w]
  have hB12 : ∀ e, (B12 K p f).map (S.θ e) = (S.ι (edgeSrc e)).range := fun e => by
    rw [B12, ← MonoidHom.range_comp, S.left e]
  have hB23 : ∀ e, (B23 K p f).map (S.θ e) = (S.ι (edgeTgt e)).range := fun e => by
    rw [B23, ← MonoidHom.range_comp, S.right e]
  have hconj : ∀ B : Subgroup (Su K p f 3),
      B.map (MulAut.conj (1 : Su K p f 3)⁻¹).toMonoidHom = B := by
    intro B
    ext x
    simp
  have es1 : edgeSrc 1 = 1 := rfl
  have et1 : edgeTgt 1 = 2 := rfl
  have es2 : edgeSrc 2 = 1 := rfl
  have et2 : edgeTgt 2 = 3 := rfl
  have hpair : ∀ i, i < 2 → UnitaryBlockStandardPair K p f (w i) (u i) (u (i + 1)) := by
    intro i hi
    interval_cases i
    · refine ⟨S.θ 1, 1, hw0.symm, hg.ker 1, Or.inr ⟨?_, ?_⟩⟩
      · rw [hconj, hB12, es1]
        exact hu1.symm
      · rw [hconj, hB23, et1]
        exact hu0.symm
    · refine ⟨S.θ 2, 1, hw1.symm, hg.ker 2, Or.inl ⟨?_, ?_⟩⟩
      · rw [hconj, hB12, es2]
        exact hu1.symm
      · rw [hconj, hB23, et2]
        exact hu2.symm
  have hcomm23 : ∀ x ∈ (S.ι 2).range, ∀ y ∈ (S.ι 3).range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact S.comm 2 3 (by decide) (by decide) (by decide) a b
  obtain ⟨θ, hθ⟩ := coherent_chain hK (autExtends hK) u w 2 hpair (fun i hi x hx y hy => by
    obtain rfl : i = 0 := by omega
    rw [hu0] at hx
    rw [show (0 + 2 : ℕ) = 2 from rfl, hu2] at hy
    exact hcomm23 x hx y hy)
  obtain ⟨hk0, -, h12_0, h23_0, hc0⟩ := hθ 0 (by omega)
  obtain ⟨hk1, -, h12_1, h23_1, -⟩ := hθ 1 (by omega)
  have hc0' : (θ 1).comp (embSUid (unitaryInvolution K p f) 2) =
      (θ 0).comp (embSUid (unitaryInvolution K p f) 0) := hc0 (by omega)
  have h23_0' : (B23 K p f).map (θ 0) = (S.ι 1).range := h23_0.trans hu1
  have h12_0' : (B12 K p f).map (θ 0) = (S.ι 2).range := h12_0.trans hu0
  have h12_1' : (B12 K p f).map (θ 1) = (S.ι 1).range := h12_1.trans hu1
  have h23_1' : (B23 K p f).map (θ 1) = (S.ι 3).range := h23_1.trans hu2
  obtain ⟨i00, rg00, i01, rg01⟩ := pair_block_inj hK hk0 h12_0' h23_0'
  obtain ⟨-, -, i11, rg11⟩ := pair_block_inj hK hk1 h12_1' h23_1'
  let ι₀ : Fin 3 → (Su K p f 2 →* G) :=
    ![(θ 0).comp (embSUid (unitaryInvolution K p f) 2),
      (θ 0).comp (embSUid (unitaryInvolution K p f) 0),
      (θ 1).comp (embSUid (unitaryInvolution K p f) 0)]
  have F'ex : ∃ F' : PhanFamily K p f G 3, F'.ι = ι₀ := by
    refine ⟨⟨ι₀, ![θ 0, θ 1, 1], ?_, ?_, ?_⟩, rfl⟩
    · intro i hi
      fin_cases i
      · rfl
      · exact hc0'
      · exact absurd hi (by decide)
    · intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact absurd hi (by decide)
    · intro i j hij a b
      fin_cases i <;> fin_cases j <;> first
        | exact absurd hij (by decide)
        | skip
      have ha : (θ 0) (embSUid (unitaryInvolution K p f) 2 a) ∈ (S.ι 2).range := by
        rw [← h12_0']
        exact ⟨_, ⟨a, rfl⟩, rfl⟩
      have hb : (θ 1) (embSUid (unitaryInvolution K p f) 0 b) ∈ (S.ι 3).range := by
        rw [← h23_1']
        exact ⟨_, ⟨b, rfl⟩, rfl⟩
      exact hcomm23 _ ha _ hb
  obtain ⟨F', hF'⟩ := F'ex
  obtain ⟨ψ, hψ, -⟩ := phanUniversal K p f hK hq (n := 3) le_rfl F'
  have hcomp : ∀ j, ψ.comp (blockEmb2 K p f 3 j) = ι₀ j := fun j => by rw [hψ j, hF']
  have hrg : ∀ j, (ι₀ j).range = (S.ι (![2, 1, 3] j)).range := by
    intro j
    fin_cases j
    · exact rg00.trans hu0
    · exact rg01.trans hu1
    · exact rg11.trans hu2
  have hinj : ∀ j, Function.Injective (ι₀ j) := by
    intro j
    fin_cases j
    · exact i00
    · exact i01
    · exact i11
  obtain ⟨s₀, hs₀⟩ := exists_normOne_ne_one hK
  have hagree : (diagTorus2 K p f).map (ι₀ 1) = (diagTorus2 K p f).map (S.ι 1) := by
    have hM : (B23 K p f).map (θ 0) = (B12 K p f).map (S.θ 2) := by
      rw [h23_0', hB12, es2]
    have hcm : ∀ x ∈ (B12 K p f).map (θ 0), ∀ y ∈ (B23 K p f).map (S.θ 2), x * y = y * x := by
      intro x hx y hy
      rw [h12_0'] at hx
      rw [hB23, et2] at hy
      exact hcomm23 x hx y hy
    have := torus_agree hK hk0 (hg.ker 2) hM hcm
    rw [map_D23, map_D12, S.left 2, es2] at this
    exact this
  set y : G := ι₀ 1 (torusTwo (unitaryInvolution K p f) s₀) with hy
  have hy1 : y ≠ 1 := by
    intro h1
    have : torusTwo (unitaryInvolution K p f) s₀ = 1 := (injective_iff_map_eq_one _).1 (hinj 1) _ h1
    have h3 : s₀ = 1 := torusTwo_injective _ (by rw [this, map_one])
    exact hs₀ (by rw [h3]; rfl)
  obtain ⟨A₁, hA₁, hA₁y⟩ : y ∈ (diagTorus2 K p f).map (S.ι 1) := by
    rw [← hagree]
    exact ⟨_, ⟨s₀, rfl⟩, rfl⟩
  obtain ⟨s₁, rfl⟩ := hA₁
  have hs₁ : ((s₁ : normOne (unitaryInvolution K p f)) : Kˣ) ≠ 1 := by
    intro h1
    have : s₁ = 1 := Subtype.ext h1
    apply hy1
    rw [← hA₁y, this, map_one, map_one]
  have hy_zero : y = (θ 0) (embSUid (unitaryInvolution K p f) 0
      (torusTwo (unitaryInvolution K p f) s₀)) := rfl
  have hy_two : y = (θ 1) (embSUid (unitaryInvolution K p f) 2
      (torusTwo (unitaryInvolution K p f) s₀)) := by
    rw [hy_zero]
    exact (DFunLike.congr_fun hc0' _).symm
  have hySs : y = S.θ 1 (embSUid (unitaryInvolution K p f) 2
      (torusTwo (unitaryInvolution K p f) s₁)) := by
    rw [← hA₁y, ← ι_src S 1]
    rfl
  have hySt : y = S.θ 2 (embSUid (unitaryInvolution K p f) 2
      (torusTwo (unitaryInvolution K p f) s₁)) := by
    rw [← hA₁y, ← ι_src S 2]
    rfl
  have hend0 : (diagTorus2 K p f).map (ι₀ 0) = (diagTorus2 K p f).map (S.ι 2) := by
    refine map_diagTorus2_eq_of_commute ((hrg 0).trans rfl) y (fun A => ?_) (fun A => ?_)
    · rw [hy_zero]
      exact mem_diagTorus2_iff_commute_zero hK hk0 hs₀ A
    · have h2A : S.ι 2 A = S.θ 1 (embSUid (unitaryInvolution K p f) 0 A) := ι_tgt S 1 A
      rw [hySs, h2A]
      exact mem_diagTorus2_iff_commute_two hK (hg.ker 1) hs₁ A
  have hend2 : (diagTorus2 K p f).map (ι₀ 2) = (diagTorus2 K p f).map (S.ι 3) := by
    refine map_diagTorus2_eq_of_commute ((hrg 2).trans rfl) y (fun A => ?_) (fun A => ?_)
    · rw [hy_two]
      exact mem_diagTorus2_iff_commute_two hK hk1 hs₀ A
    · have h3A : S.ι 3 A = S.θ 2 (embSUid (unitaryInvolution K p f) 0 A) := ι_tgt S 2 A
      rw [hySt, h3A]
      exact mem_diagTorus2_iff_commute_two hK (hg.ker 2) hs₁ A
  refine ⟨ψ, by decide, fun j A => ?_, fun j r hr => ?_, fun j => ?_, fun j => ?_⟩
  · have hA : ψ (blockEmb2 K p f 3 j A) = ι₀ j A := DFunLike.congr_fun (hcomp j) A
    rw [hA]
    exact (hrg j) ▸ ⟨A, rfl⟩
  · rw [← hrg j] at hr
    obtain ⟨A, hA⟩ := hr
    have hA' : ψ (blockEmb2 K p f 3 j A) = ι₀ j A := DFunLike.congr_fun (hcomp j) A
    exact ⟨A, by rw [hA', hA]⟩
  · rw [hcomp]
    exact hinj j
  · rw [hcomp, MonoidHom.range_comp]
    show (diagTorus2 K p f).map (ι₀ j) = ((S.ι (![2, 1, 3] j)).comp (torusTwo _)).range
    rw [MonoidHom.range_comp]
    fin_cases j
    · exact hend0
    · exact hagree
    · exact hend2

theorem nullOn_123 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S)
    (h2 : (2 : K) ≠ 0) : NullOnPhan S {1, 2, 3} := by
  obtain ⟨ψ, hch⟩ := exists_chain_123 hK hq hg
  intro x γ hγ hJ hend
  refine hch.twoHomotopic_nil hK (by omega) hg h2 x γ hγ (fun j hj => ?_) hend
  have := hJ j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with rfl | rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

end Mixed

end CFSG.ClassicalInvolution.PhanG
