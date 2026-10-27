module

public import CFSG.CGT.PushingUpLit.SYMB.JoinBlock
public import CFSG.CGT.PushingUpLit.SYMB.Schur
public import CFSG.CGT.PushingUpLit.SYMB.BlockFacts

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {n : ℕ} {G T V : Subgroup Γ} {φ : ↥G →* Equiv.Perm (Fin n)}
  {ψ : ↥V →* ↥(G6.coreMod n)} {T' : Set (Equiv.Perm (Fin n))} {E : Subgroup Γ}

namespace SymJoin

theorem ker_le_commutator [Finite Γ] (S : SymSetting G T V n φ ψ T')
    (h : SymJoin G T V φ ψ E) (h5 : 5 ≤ n)
    (hK2 : IsPGroup 2 ↥(E ⊓ Subgroup.centralizer (V : Set Γ)))
    {p : Fin 4 → Fin n} (hp : Function.Injective p) {a b : Γ} (haE : a ∈ E) (hbE : b ∈ E)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (haφ : φ ⟨a, h.le haE⟩ = Equiv.swap (p 0) (p 2) * Equiv.swap (p 0) (p 1))
    (hbφ : φ ⟨b, h.le hbE⟩ = Equiv.swap (p 0) (p 3) * Equiv.swap (p 0) (p 1))
    (hab : (a * b) ^ 2 ∈ ⁅E ⊓ Subgroup.centralizer (V : Set Γ), E⁆) :
    E ⊓ Subgroup.centralizer (V : Set Γ) ≤ ⁅E ⊓ Subgroup.centralizer (V : Set Γ), E⁆ := by
  classical
  have hEG : E ≤ G := h.le
  have hKE : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ E := inf_le_left
  let η : ↥E →* alternatingGroup (Fin n) := altRestrict φ hEG fun _ he => h.map_mem_alt he
  have hηs : Function.Surjective η := altRestrict_surjective h
  have hηker : η.ker = (E ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h1
      have h2 : φ ⟨e, hEG e.2⟩ = 1 := congrArg Subtype.val h1
      have h3 : (⟨e, hEG e.2⟩ : ↥G) ∈ φ.ker := h2
      rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h3
      exact ⟨e.2, h3.2⟩
    · rintro ⟨-, hec⟩
      have h3 : (⟨e, hEG e.2⟩ : ↥G) ∈ φ.ker := by
        rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨hEG e.2, hec⟩
      have h4 : φ ⟨e, hEG e.2⟩ = 1 := h3
      exact Subtype.ext h4
  have hK2η : IsPGroup 2 ↥η.ker := by
    rw [hηker]
    exact hK2.of_equiv (Subgroup.subgroupOfEquivOfLe hKE).symm
  have hcomm : (⁅(E ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf E,
      (⊤ : Subgroup ↥E)⁆).map E.subtype = ⁅E ⊓ Subgroup.centralizer (V : Set Γ), E⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKE, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hab' : ((⟨a, haE⟩ : ↥E) * ⟨b, hbE⟩) ^ 2 ∈ ⁅η.ker, (⊤ : Subgroup ↥E)⁆ := by
    rw [hηker, ← Subgroup.mem_map_iff_mem E.subtype_injective, hcomm]
    simpa using hab
  have hres := ker_le_commutator_of_lifts h5 η hηs h.residual hK2η hp (a := ⟨a, haE⟩)
    (b := ⟨b, hbE⟩) (Subtype.ext (by simpa using ha)) (Subtype.ext (by simpa using hb)) haφ hbφ
    hab'
  intro k hk
  have hk' : (⟨k, hKE hk⟩ : ↥E) ∈ η.ker := by
    rw [hηker]
    exact hk
  have hk2 : k ∈ (⁅η.ker, (⊤ : Subgroup ↥E)⁆).map E.subtype := ⟨⟨k, hKE hk⟩, hres hk', rfl⟩
  rw [hηker, hcomm] at hk2
  exact hk2

end SymJoin

theorem swap_mul_eq {p0 p1 p2 p3 : Fin n} (h03 : p0 ≠ p3) (h13 : p1 ≠ p3) :
    Equiv.swap p0 p2 * Equiv.swap p0 p1 * (Equiv.swap p0 p3 * Equiv.swap p0 p1) =
      Equiv.swap p0 p2 * Equiv.swap p1 p3 := by
  have h := Equiv.swap_apply_apply (Equiv.swap p0 p1) p0 p3
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h03.symm h13.symm] at h
  calc Equiv.swap p0 p2 * Equiv.swap p0 p1 * (Equiv.swap p0 p3 * Equiv.swap p0 p1)
      = Equiv.swap p0 p2 * (Equiv.swap p0 p1 * Equiv.swap p0 p3 * (Equiv.swap p0 p1)⁻¹) := by
        rw [Equiv.swap_inv]; group
    _ = Equiv.swap p0 p2 * Equiv.swap p1 p3 := by rw [h]

theorem swap_mul_sq_eq_one {p0 p1 p2 p3 : Fin n} (h01 : p0 ≠ p1) (h03 : p0 ≠ p3)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) :
    (Equiv.swap p0 p2 * Equiv.swap p0 p1 * (Equiv.swap p0 p3 * Equiv.swap p0 p1)) ^ 2 = 1 := by
  have e1 := swap_mul_eq (p2 := p2) h03 h13
  have hd : Equiv.swap p0 p2 * Equiv.swap p1 p3 = Equiv.swap p1 p3 * Equiv.swap p0 p2 := by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  rw [e1, sq]
  calc Equiv.swap p0 p2 * Equiv.swap p1 p3 * (Equiv.swap p0 p2 * Equiv.swap p1 p3)
      = Equiv.swap p0 p2 * (Equiv.swap p1 p3 * Equiv.swap p0 p2) * Equiv.swap p1 p3 := by group
    _ = Equiv.swap p0 p2 * (Equiv.swap p0 p2 * Equiv.swap p1 p3) * Equiv.swap p1 p3 := by rw [hd]
    _ = 1 := by
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul, Equiv.swap_mul_self]

theorem exists_lifts_block [Finite Γ] (S : SymSetting G T V n φ ψ T') {F : Subgroup Γ}
    (hF : IsBTBlock G T F) (hFn : ¬ F ≤ cStarIn G T) {Ω : Finset (Fin n)}
    (hFΩ : imgG G φ F = altOn Ω) {p : Fin 4 → Fin n} (hp : Function.Injective p)
    (hpΩ : ∀ i, p i ∈ Ω) :
    ∃ (a : Γ) (ha : a ∈ F) (b : Γ) (hb : b ∈ F), a ^ 3 = 1 ∧ b ^ 3 = 1 ∧
      φ ⟨a, hF.le ha⟩ = Equiv.swap (p 0) (p 2) * Equiv.swap (p 0) (p 1) ∧
      φ ⟨b, hF.le hb⟩ = Equiv.swap (p 0) (p 3) * Equiv.swap (p 0) (p 1) ∧
      (a * b) ^ 2 ∈ pCoreOf 2 F := by
  classical
  have hFG : F ≤ G := hF.le
  have hmem : ∀ f : ↥F, φ ⟨f, hFG f.2⟩ ∈ altOn Ω := fun f => by
    rw [← hFΩ]
    exact mem_imgG.2 ⟨f, hFG f.2, f.2, rfl⟩
  let ρ : ↥F →* ↥(altOn Ω) := (φ.comp (Subgroup.inclusion hFG)).codRestrict (altOn Ω) hmem
  have hρs : Function.Surjective ρ := by
    intro y
    have hy : (y : Equiv.Perm (Fin n)) ∈ imgG G φ F := by
      rw [hFΩ]
      exact y.2
    obtain ⟨g, hgG, hgF, hφ⟩ := mem_imgG.1 hy
    exact ⟨⟨g, hgF⟩, Subtype.ext hφ⟩
  have hker : ∀ x : ↥F, ρ x = 1 → (x : Γ) ∈ pCoreOf 2 F := by
    intro x hx
    have h1 : φ ⟨x, hFG x.2⟩ = 1 := congrArg Subtype.val hx
    have h2 : (⟨x, hFG x.2⟩ : ↥G) ∈ φ.ker := h1
    rw [S.data.φ_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h2
    rw [← sym_inf_centralizer_block S hF hFn]
    exact ⟨x.2, h2.2⟩
  have hρk : IsPGroup 2 ↥ρ.ker := by
    let ι : ↥ρ.ker →* ↥(pCoreOf 2 F) :=
      (F.subtype.comp ρ.ker.subtype).codRestrict (pCoreOf 2 F) fun x => hker x.1 x.2
    have hι : Function.Injective ι := fun x y hxy => by
      have h := congrArg Subtype.val hxy
      apply Subtype.ext
      apply Subtype.ext
      exact h
    exact (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 F).of_injective ι hι
  have h01 : p 0 ≠ p 1 := hp.ne (by decide)
  have h02 : p 0 ≠ p 2 := hp.ne (by decide)
  have h03 : p 0 ≠ p 3 := hp.ne (by decide)
  have h12 : p 1 ≠ p 2 := hp.ne (by decide)
  have h13 : p 1 ≠ p 3 := hp.ne (by decide)
  have h23 : p 2 ≠ p 3 := hp.ne (by decide)
  have hc₁ : cyc (p 0) (p 2) (p 1) ∈ altOn Ω :=
    cyc_mem_altOn (hpΩ 0) (hpΩ 2) (hpΩ 1) h02 h01 h12.symm
  have hc₂ : cyc (p 0) (p 3) (p 1) ∈ altOn Ω :=
    cyc_mem_altOn (hpΩ 0) (hpΩ 3) (hpΩ 1) h03 h01 h13.symm
  have hc₁3 : (⟨cyc (p 0) (p 2) (p 1), hc₁⟩ : ↥(altOn Ω)) ^ 3 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one (cyc (p 0) (p 2) (p 1))
    rw [(cyc_isThreeCycle h02 h01 h12.symm).orderOf] at this
    simpa using this
  have hc₂3 : (⟨cyc (p 0) (p 3) (p 1), hc₂⟩ : ↥(altOn Ω)) ^ 3 = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one (cyc (p 0) (p 3) (p 1))
    rw [(cyc_isThreeCycle h03 h01 h13.symm).orderOf] at this
    simpa using this
  obtain ⟨a₀, ha₀, ha₀3⟩ := exists_order_three_lift ρ hρs hρk hc₁3
  obtain ⟨b₀, hb₀, hb₀3⟩ := exists_order_three_lift ρ hρs hρk hc₂3
  have hsq : ρ ((a₀ * b₀) ^ 2) = 1 := by
    rw [map_pow, map_mul, ha₀, hb₀]
    apply Subtype.ext
    simpa [cyc] using swap_mul_sq_eq_one h01 h03 h12 h13 h23
  refine ⟨a₀, a₀.2, b₀, b₀.2, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val ha₀3
  · simpa using congrArg Subtype.val hb₀3
  · exact congrArg Subtype.val ha₀
  · exact congrArg Subtype.val hb₀
  · simpa using hker _ hsq

end CFSG.CGT.PushingUpLit.SYMB
