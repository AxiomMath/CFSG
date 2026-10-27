module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatY

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization

section Permutations

theorem five_points_exhaust {Ω : Type*} [Fintype Ω] (h5 : Fintype.card Ω = 5)
    {a b c d ω : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hωa : ω ≠ a) (hωb : ω ≠ b) (hωc : ω ≠ c) (hωd : ω ≠ d) :
    ∀ x : Ω, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = ω := by
  let f : Fin 5 → Ω := ![a, b, c, d, ω]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
      first | exact absurd hij ‹_› | exact absurd hij.symm ‹_›
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [h5]⟩
  intro x
  obtain ⟨i, rfl⟩ := hbij.2 x
  fin_cases i <;> simp [f]

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_moves_omega (h5 : Fintype.card Ω = 5)
    {a b c d ω : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hωa : ω ≠ a) (hωb : ω ≠ b) (hωc : ω ≠ c) (hωd : ω ≠ d)
    (F : Subgroup (Equiv.Perm Ω)) (hF : Nat.card F = 3)
    (hnorm : Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)) ≤
      Subgroup.normalizer (F : Set (Equiv.Perm Ω))) :
    ∃ g ∈ F, g ω ≠ ω := by
  by_contra hcon
  have hfix : ∀ g ∈ F, g ω = ω := fun g hg => by_contra fun h => hcon ⟨g, hg, h⟩
  have hall := five_points_exhaust h5 hab hac had hbc hbd hcd hωa hωb hωc hωd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 F := IsPGroup.of_card (n := 1) (by simpa using hF)
  have hmod := hpg.card_modEq_card_fixedPoints (α := Ω)
  set Fix := MulAction.fixedPoints F Ω with hFix
  have hω : ω ∈ Fix := fun g => hfix g g.2
  have hcardΩ : Nat.card Ω = 5 := by simpa using h5
  have hne : Fix ≠ Set.univ := by
    intro hu
    have hone : ∀ g : F, (g : Equiv.Perm Ω) = 1 := fun g => by
      ext x
      have := hu ▸ (Set.mem_univ x)
      exact this g
    have : Nat.card F = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => Subtype.ext ((hone x).trans (hone y).symm)⟩, ⟨1⟩⟩
    omega
  have hlt : Nat.card Fix < 5 := by
    have hle : Fix.ncard ≤ 5 := by
      rw [← hcardΩ, ← Set.ncard_univ]
      exact Set.ncard_le_ncard (Set.subset_univ _)
    rw [Nat.card_coe_set_eq]
    refine lt_of_le_of_ne hle fun h => hne ?_
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_univ, hcardΩ, h]
  have hcard2 : Fix.ncard = 2 := by
    rw [Nat.card_coe_set_eq] at hlt hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨x, y, hxy, hxyeq⟩ := Set.ncard_eq_two.1 hcard2
  obtain ⟨p, hpω, hFixeq⟩ : ∃ p, p ≠ ω ∧ Fix = {ω, p} := by
    have hωxy : ω ∈ ({x, y} : Set Ω) := hxyeq ▸ hω
    rcases hωxy with rfl | rfl
    · exact ⟨y, fun h => hxy h.symm, by rw [hxyeq]⟩
    · exact ⟨x, hxy, by rw [hxyeq, Set.pair_comm]⟩
  have hinv : ∀ e ∈ Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)),
      ∀ z ∈ Fix, e z ∈ Fix := by
    intro e he z hz g
    have hen := hnorm he
    have h1 : e⁻¹ * (g : Equiv.Perm Ω) * e ∈ F := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hen) (g : Equiv.Perm Ω)).1 g.2
      simpa using this
    have h2 := hz ⟨_, h1⟩
    have h3 : (e⁻¹ * (g : Equiv.Perm Ω) * e) z = z := h2
    have h4 : (g : Equiv.Perm Ω) (e z) = e z := by
      have := congrArg e h3
      simpa [Equiv.Perm.mul_apply] using this
    exact h4
  have hpab : Equiv.swap a b p = p := by
    have h1 := hinv (Equiv.swap a b) (Subgroup.subset_closure (by simp)) p
      (hFixeq ▸ Or.inr rfl)
    rw [hFixeq] at h1
    rcases h1 with h | h
    · exfalso
      have : Equiv.swap a b ω = ω := by
        rw [Equiv.swap_apply_of_ne_of_ne hωa hωb]
      exact hpω ((Equiv.swap a b).injective (h.trans this.symm))
    · exact h
  have hpcd : Equiv.swap c d p = p := by
    have h1 := hinv (Equiv.swap c d) (Subgroup.subset_closure (by simp)) p
      (hFixeq ▸ Or.inr rfl)
    rw [hFixeq] at h1
    rcases h1 with h | h
    · exfalso
      have : Equiv.swap c d ω = ω := by
        rw [Equiv.swap_apply_of_ne_of_ne hωc hωd]
      exact hpω ((Equiv.swap c d).injective (h.trans this.symm))
    · exact h
  rcases hall p with rfl | rfl | rfl | rfl | rfl
  · simp at hpab
    exact hab hpab.symm
  · simp at hpab
    exact hab hpab
  · simp at hpcd
    exact hcd hpcd.symm
  · simp at hpcd
    exact hcd hpcd
  · exact hpω rfl

theorem not_le_normalizer_of_seed {Γ : Type*} [Group Γ]
    (h5 : Fintype.card Ω = 5) (B Fs0 A0 Y : Subgroup Γ) (ψ : ↥B ≃* Equiv.Perm Ω)
    {a b c d ω : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hωa : ω ≠ a) (hωb : ω ≠ b) (hωc : ω ≠ c) (hωd : ω ≠ d)
    (hFB : Fs0 ≤ B) (hF3 : Nat.card Fs0 = 3)
    (hAn : A0 ≤ Subgroup.normalizer (Fs0 : Set Γ))
    (hA : (A0.subgroupOf B).map ψ.toMonoidHom =
      Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)))
    (hY1 : ∀ y : ↥B, (y : Γ) ∈ A0 → ψ y ∈ alternatingGroup Ω → (y : Γ) ∈ Y)
    (hY3 : ∀ y : ↥B, (y : Γ) ∈ Y → ψ y ω = ω) :
    ¬ Fs0 ≤ Subgroup.normalizer (Y : Set Γ) := by
  intro hFY
  set F'' : Subgroup (Equiv.Perm Ω) := (Fs0.subgroupOf B).map ψ.toMonoidHom with hF''
  have hcard : Nat.card F'' = 3 := by
    rw [hF'', Subgroup.card_map_of_injective ψ.injective, ← hF3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFB).toEquiv
  have hE : Subgroup.closure ({Equiv.swap a b, Equiv.swap c d} : Set (Equiv.Perm Ω)) ≤
      Subgroup.normalizer (F'' : Set (Equiv.Perm Ω)) := by
    rw [← hA]
    refine map_le_normalizer_map_of_le ψ ?_
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have := Subgroup.mem_normalizer_iff.1 (hAn hy) (z : Γ)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  obtain ⟨g, hgF, hgω⟩ :=
    exists_moves_omega h5 hab hac had hbc hbd hcd hωa hωb hωc hωd F'' hcard hE
  obtain ⟨x, hx, rfl⟩ := hgF
  have hu : Equiv.swap a b * Equiv.swap c d ∈ (A0.subgroupOf B).map ψ.toMonoidHom := by
    rw [hA]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  obtain ⟨y0, hy0, hy0u⟩ := hu
  have hualt : Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup Ω := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hcd]
    decide
  have hy0Y : (y0 : Γ) ∈ Y := hY1 y0 hy0 (by
    have : ψ y0 = Equiv.swap a b * Equiv.swap c d := hy0u
    rw [this]
    exact hualt)
  have hxn : (x : Γ) ∈ Subgroup.normalizer (Y : Set Γ) := hFY hx
  have hconj : (x : Γ) * y0 * (x : Γ)⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.1 hxn (y0 : Γ)).1 hy0Y
  have hz := hY3 (x * y0 * x⁻¹) (by simpa using hconj)
  have hψz : ψ (x * y0 * x⁻¹) = ψ x * (Equiv.swap a b * Equiv.swap c d) * (ψ x)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    have : ψ y0 = Equiv.swap a b * Equiv.swap c d := hy0u
    rw [this]
  rw [hψz] at hz
  set g : Equiv.Perm Ω := ψ x with hg
  have hq : (Equiv.swap a b * Equiv.swap c d) (g⁻¹ ω) = g⁻¹ ω := by
    have h1 : g ((Equiv.swap a b * Equiv.swap c d) (g⁻¹ ω)) = ω := by
      simpa [Equiv.Perm.mul_apply] using hz
    have h2 := congrArg (fun y => g⁻¹ y) h1
    simpa using h2
  have hall := five_points_exhaust h5 hab hac had hbc hbd hcd hωa hωb hωc hωd (g⁻¹ ω)
  rcases hall with h | h | h | h | h
  · rw [h] at hq
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac had] at hq
    exact hab hq.symm
  · rw [h] at hq
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hbc hbd] at hq
    exact hab hq
  · rw [h] at hq
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)] at hq
    exact hcd hq.symm
  · rw [h] at hq
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)] at hq
    exact hcd hq
  · apply hgω
    have : g⁻¹ ω = ω := h
    have h2 := congrArg (fun y => g y) this
    simpa using h2.symm

end Permutations

section Groups

theorem relIndex_sup_seed {Γ : Type*} [Group Γ] [Finite Γ] {Fs D : Subgroup Γ}
    (hF : Nat.card Fs = 3) (hD : IsPGroup 2 D) (hnorm : D ≤ Subgroup.normalizer (Fs : Set Γ)) :
    D.relIndex (Fs ⊔ D) = 3 := by
  set N := Fs ⊔ D with hN
  have hFN : Fs ≤ N := le_sup_left
  have hDN : D ≤ N := le_sup_right
  have hNn : N ≤ Subgroup.normalizer (Fs : Set Γ) := sup_le Subgroup.le_normalizer hnorm
  have hFn : (Fs.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hFN).2 hNn
  have hsup : D.subgroupOf N ⊔ Fs.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDN hFN, sup_comm, ← hN, Subgroup.subgroupOf_self]
  have hFD : Fs ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have h3 : orderOf x ∣ 3 := by
      have := orderOf_dvd_natCard (⟨x, hx.1⟩ : Fs)
      rwa [hF, Subgroup.orderOf_mk] at this
    obtain ⟨k, hk⟩ := hD ⟨x, hx.2⟩
    have h2 : orderOf x ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg (fun y : D => (y : Γ)) hk
      simpa using this
    have h1 : orderOf x ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h3 h2
    have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    rw [hc.gcd_eq_one] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have hdisj : Fs.subgroupOf N ⊓ D.subgroupOf N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have : (x : Γ) ∈ Fs ⊓ D := ⟨hx.1, hx.2⟩
    rw [hFD, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have h1 : (Fs.subgroupOf N).relIndex (D.subgroupOf N ⊔ Fs.subgroupOf N) =
      (Fs.subgroupOf N).relIndex (D.subgroupOf N) := Subgroup.relIndex_sup_right _ _
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 : (Fs.subgroupOf N).relIndex (D.subgroupOf N) = Nat.card (D.subgroupOf N) := by
    rw [← Subgroup.inf_relIndex_right, hdisj, Subgroup.relIndex_bot_left]
  have hFc : Nat.card (Fs.subgroupOf N) = 3 := by
    rw [← hF]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  have h3 : Nat.card N = 3 * Nat.card (D.subgroupOf N) := by
    rw [← Subgroup.card_mul_index (Fs.subgroupOf N), hFc, h1, h2]
  have h4 : Nat.card N = Nat.card (D.subgroupOf N) * (D.subgroupOf N).index :=
    (Subgroup.card_mul_index (D.subgroupOf N)).symm
  have hpos : 0 < Nat.card (D.subgroupOf N) := Nat.card_pos
  have h5 : (D.subgroupOf N).index = 3 := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← h4, h3, mul_comm]
  exact h5

variable {G Q : Type*} [Group G] [Group Q]

theorem isSylowTwoOf_of_map_ker [Finite G] [Finite Q] (ρ : G →* Q) {H S : Subgroup G}
    (hSH : S ≤ H) (hS : IsPGroup 2 S) (hK : IsSylowTwoOf (S ⊓ ρ.ker) (H ⊓ ρ.ker))
    (hQ : IsSylowTwoOf (S.map ρ) (H.map ρ)) : IsSylowTwoOf S H := by
  obtain ⟨-, -, hKmax⟩ := A4.isSylowTwoOf_iff_maximal.1 hK
  obtain ⟨-, -, hQmax⟩ := A4.isSylowTwoOf_iff_maximal.1 hQ
  refine A4.isSylowTwoOf_iff_maximal.2 ⟨hSH, hS, fun P hPH hP hSP => ?_⟩
  intro x hx
  have hPQ : P.map ρ ≤ S.map ρ :=
    hQmax (P.map ρ) (Subgroup.map_mono hPH) (hP.map ρ) (Subgroup.map_mono hSP)
  obtain ⟨s, hs, hsx⟩ := hPQ ⟨x, hx, rfl⟩
  have hsP : s ∈ P := hSP hs
  have hk0 : ρ (s⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hsx, inv_mul_cancel]
  have hk : s⁻¹ * x ∈ P ⊓ ρ.ker := ⟨P.mul_mem (P.inv_mem hsP) hx, MonoidHom.mem_ker.2 hk0⟩
  have hkS : s⁻¹ * x ∈ S ⊓ ρ.ker :=
    hKmax (P ⊓ ρ.ker) (inf_le_inf hPH le_rfl) hP.to_inf_left (inf_le_inf hSP le_rfl) hk
  have hx' : x = s * (s⁻¹ * x) := by group
  rw [hx']
  exact S.mul_mem hs hkS.1

end Groups

section Rho

variable {G : Type} [Group G] {V : Subgroup G}

theorem rho_top_eq_conjNormal [V.Normal] (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    (g : G) : rho V ⊤ hX ⟨g, Subgroup.mem_top g⟩ = MulAut.conjNormal (H := V) g :=
  BlueprintB2.conjAct_eq_conjNormal V ⟨g, hX (Subgroup.mem_top g)⟩

theorem mem_rhoPreimage_top_conj [V.Normal]
    (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) {N : Subgroup (MulAut V)} {x : G} :
    x ∈ rhoPreimage V ⊤ hX N ↔ MulAut.conjNormal (H := V) x ∈ N := by
  rw [mem_rhoPreimage_top, rho_top_eq_conjNormal]

theorem ker_conjNormal [V.Normal] (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) :
    (MulAut.conjNormal (H := V)).ker = Subgroup.centralizer (V : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, ← rho_top_eq_conjNormal hX g]
  exact rho_eq_one_iff hX ⟨g, Subgroup.mem_top g⟩

end Rho

section Main

variable {G : Type} [Group G] [Finite G]

theorem autOn_delH0
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)} (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    {Fs : Subgroup (MulAut V)} (hFs : Fs ≤ Lc i) :
    autOn (delH0 R V ctx.hX Fs) V = Fs ⊔ autOn (baum R) V := by
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hbridge := even_SL2_original_bridge ctx.setting ctx.comps
  have hLcK : Lc i ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V := by
    rw [hbridge.K_eq, hbridge.K_prod]
    exact le_iSup Lc i
  have hN : Fs ⊔ autOn (baum R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) V :=
    sup_le ((hFs.trans hLcK).trans (autOn_le_autOn V le_sup_left))
      (autOn_le_autOn V le_sup_right)
  ext φ
  rw [autOn_eq_map_conjNormal V]
  constructor
  · rintro ⟨x, ⟨_, hx⟩, rfl⟩
    exact (mem_rhoPreimage_top_conj hX).1 hx
  · intro hφ
    have hφ' := hN hφ
    rw [autOn_eq_map_conjNormal V] at hφ'
    obtain ⟨x, hxLS, rfl⟩ := hφ'
    exact ⟨x, ⟨hxLS, (mem_rhoPreimage_top_conj hX).2 hφ⟩, rfl⟩

theorem delH0_sylow
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)} (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    {Fs : Subgroup (MulAut V)} (hcore : DeletedBaumannCore R V) (hseed : DelSeed R V (Lc i) Fs) :
    IsSylowTwoOf (baum R) (delH0 R V ctx.hX Fs) := by
  have hX := ctx.hX
  have hS := ctx.setting
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective
  have hSR : baum R ≤ R := inf_le_left
  have hS2 : IsPGroup 2 (baum R) := hS.sylow.2.1.to_le hSR
  have hDmap : autOn (baum R) V = (baum R).map (MulAut.conjNormal (H := V)) :=
    autOn_eq_map_conjNormal V _
  have hker : (MulAut.conjNormal (H := V)).ker = Subgroup.centralizer (V : Set G) :=
    ker_conjNormal hX
  have hSH : baum R ≤ delH0 R V hX Fs := by
    refine le_inf le_sup_right fun s hs => ?_
    refine (mem_rhoPreimage_top_conj hX).2 ?_
    have hs' : MulAut.conjNormal (H := V) s ∈ autOn (baum R) V := by
      rw [hDmap]
      exact Subgroup.mem_map_of_mem _ hs
    exact Subgroup.mem_sup_right hs'
  have hH0C : delH0 R V hX Fs ⊓ Subgroup.centralizer (V : Set G) =
      (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, (mem_rhoPreimage_top_conj hX).2 ?_⟩, h2⟩
      have h3 : MulAut.conjNormal (H := V) x = 1 :=
        MonoidHom.mem_ker.1 (by rw [hker]; exact h2)
      rw [h3]
      exact Subgroup.one_mem _
  have hK : IsSylowTwoOf (baum R ⊓ (MulAut.conjNormal (H := V)).ker)
      (delH0 R V hX Fs ⊓ (MulAut.conjNormal (H := V)).ker) := by
    rw [hker, hH0C]
    exact hcore.CS_sylow
  have himage := autOn_delH0 ctx i hseed.le
  have hDp : IsPGroup 2 (autOn (baum R) V) := by
    rw [hDmap]
    exact hS2.map _
  have hrel : (autOn (baum R) V).relIndex (Fs ⊔ autOn (baum R) V) = 3 :=
    relIndex_sup_seed hseed.card hDp hseed.normalized
  have hQ : IsSylowTwoOf ((baum R).map (MulAut.conjNormal (H := V)))
      ((delH0 R V hX Fs).map (MulAut.conjNormal (H := V))) := by
    rw [← hDmap, ← autOn_eq_map_conjNormal V, himage]
    refine ⟨le_sup_right, hDp, ?_⟩
    show ¬ 2 ∣ (autOn (baum R) V).relIndex (Fs ⊔ autOn (baum R) V)
    rw [hrel]
    decide
  exact isSylowTwoOf_of_map_ker (MulAut.conjNormal (H := V)) hSH hS2 hK hQ

theorem delH0_not_le_M
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)} (ctx : DelCtx R M V n F r Lc) (i : Fin r)
    {Fs : Subgroup (MulAut V)} (hseed : DelSeed R V (Lc i) Fs) :
    ¬ delH0 R V ctx.hX Fs ≤ M := by
  intro hH0M
  classical
  have hS := ctx.setting
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS ctx.comps
  have hbridge := even_SL2_original_bridge hS ctx.comps
  set ψ := (binPsi θ).toMonoidHom with hψ
  set L := oddOrderSubgroup (⊤ : Subgroup G)
  have hbK : autOn L V = oddOrderSubgroup (autOn (⊤ : Subgroup G) V) := hbridge.K_eq
  have hKL : (autOn L V).map ψ = oddGen ((autOn (⊤ : Subgroup G) V).map ψ) := by
    rw [hbK]
    exact map_closure_odd (binPsi θ) (autOn (⊤ : Subgroup G) V)
  have hdelF : DeletedFamily ((autOn (⊤ : Subgroup G) V).map ψ) n r
      (fun i => (Lc i).map ψ) := by
    rcases hmax.offenders.family.alternatives with ⟨hnat, -⟩ | ⟨hdelF, -⟩
    · exfalso
      apply ctx.deleted
      have h1 := (himg.natural hnat).2.1.1
      rw [← hKL] at h1
      exact (Subgroup.map_le_map_iff_of_injective (binPsi θ).injective).1 h1
    · exact hdelF
  have common := hmax.offenders.family.common
  have hKeq := hmax.offenders.family.layer.K_eq
  obtain ⟨-, -, ψi, _, Ai, h5, hD, hdata⟩ := himg.deleted hdelF
  obtain ⟨a, b, c, d, ω, hab, hac, had, hbc, hbd, hcd, hωa, hωb, hωc, hωd, hmap, hfixω, -⟩ :=
    (hdata i).2.2.2
  have halt := (hdata i).2.1
  have hAT := (hdata i).2.2.1
  have hFsM : Fs ≤ autOn M V := by
    intro f hf
    have hf' : f ∈ autOn (delH0 R V ctx.hX Fs) V := by
      rw [autOn_delH0 ctx i hseed.le]
      exact Subgroup.mem_sup_left hf
    exact autOn_le_autOn V hH0M hf'
  have hMn : Fs.map ψ ≤ Subgroup.normalizer
      ((((autOn R V).map ψ) ⊓ oddGen ((autOn (⊤ : Subgroup G) V).map ψ) : Subgroup _) :
        Set (W ≃ₗ[ZMod 2] W)) := by
    intro x hx
    have hxM : x ∈ (autOn M V).map ψ := Subgroup.map_mono hFsM hx
    rw [hmax.M_eq_normalizer] at hxM
    exact hxM.1
  have hFB : Fs.map ψ ≤ blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc i).map ψ) :=
    (Subgroup.map_mono hseed.le).trans (common.L_le_B i)
  have hF3 : Nat.card (Fs.map ψ) = 3 := by
    rw [Subgroup.card_map_of_injective (binPsi θ).injective]
    exact hseed.card
  have hDS : (autOn (baum R) V).map ψ = ⨆ j, Ai j := himg.baumann_eq.symm.trans hD
  have hAn : Ai i ≤ Subgroup.normalizer ((Fs.map ψ : Subgroup (W ≃ₗ[ZMod 2] W)) :
      Set (W ≃ₗ[ZMod 2] W)) := by
    refine (le_iSup Ai i).trans ?_
    rw [← hDS]
    exact map_le_normalizer_map_of_le (binPsi θ) hseed.normalized
  have hY1 : ∀ y : ↥(blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc i).map ψ)),
      (y : W ≃ₗ[ZMod 2] W) ∈ Ai i → ψi i y ∈ alternatingGroup (ℙ F (Fin 2 → F)) →
      (y : W ≃ₗ[ZMod 2] W) ∈ ((autOn R V).map ψ) ⊓
        oddGen ((autOn (⊤ : Subgroup G) V).map ψ) := by
    intro y hy hyalt
    refine ⟨(hAT hy).1, ?_⟩
    rw [← halt] at hyalt
    obtain ⟨z, hz, hzy⟩ := hyalt
    have hzy' : z = y := (ψi i).injective hzy
    subst hzy'
    rw [hKeq]
    exact le_iSup (fun j => (Lc j).map ψ) i hz
  have hY3 : ∀ y : ↥(blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc i).map ψ)),
      (y : W ≃ₗ[ZMod 2] W) ∈ ((autOn R V).map ψ) ⊓
        oddGen ((autOn (⊤ : Subgroup G) V).map ψ) → ψi i y ω = ω := by
    intro y hy
    exact hfixω _ ⟨y, ⟨hy.1, y.2⟩, rfl⟩
  exact not_le_normalizer_of_seed h5 _ (Fs.map ψ) (Ai i) _ (ψi i) hab hac had hbc hbd hcd hωa hωb
    hωc hωd hFB hF3 hAn hmap hY1 hY3 hMn

theorem delH0Prop
    : DelH0Prop := by
  intro G _ _ R M V n F _ r Lc ctx i Fs hcore _ hseed
  exact ⟨delH0_sylow ctx i hcore hseed, delH0_not_le_M ctx i hseed⟩

end Main

end CFSG.QuasithinUnique.Setup.Lift
