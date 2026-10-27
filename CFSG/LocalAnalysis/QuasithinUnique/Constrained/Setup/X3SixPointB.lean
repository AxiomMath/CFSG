module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Orbits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bGroup

public section

namespace CFSG.QuasithinUnique.Setup.X3

open Equiv Subgroup

section LemmaK

variable {Γ : Type*} [Group Γ] {O : Type*} [Fintype O] [DecidableEq O]

theorem injective_and_range_alt (e : Γ ≃* alternatingGroup (Fin 6)) (ψ : Γ →* Perm O)
    (hO : Fintype.card O = 6) (hψ : ψ ≠ 1) :
    Function.Injective ψ ∧ ψ.range = alternatingGroup O := by
  have hfin : Finite Γ := finite_of_equiv_alt6 e
  have hsimple : IsSimpleGroup Γ := isSimpleGroup_of_equiv_alt6 e
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      apply hψ
      ext g : 1
      have : g ∈ ψ.ker := by rw [h]; trivial
      simpa using this
  refine ⟨hinj, ?_⟩
  let sg : Γ →* ℤˣ := Perm.sign.comp ψ
  have hker : sg.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal sg.ker with h | h
    · exfalso
      have hsginj : Function.Injective sg := (MonoidHom.ker_eq_bot_iff sg).mp h
      have hle := Nat.card_le_card_of_injective sg hsginj
      rw [card_of_equiv_alt6 e, Nat.card_eq_fintype_card, Fintype.card_units_int] at hle
      omega
    · exact h
  have hle : ψ.range ≤ alternatingGroup O := by
    rintro _ ⟨g, rfl⟩
    rw [Perm.mem_alternatingGroup]
    have : g ∈ sg.ker := by rw [hker]; trivial
    simpa [sg] using this
  have hnt : Nontrivial O := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hO]; norm_num
  refine (Subgroup.eq_of_le_of_card_ge hle ?_)
  have h1 := two_mul_nat_card_alternatingGroup (α := O)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := O), hO] at h1
  have h720 : (6 : ℕ).factorial = 720 := by decide
  rw [h720] at h1
  have h2 : Nat.card ψ.range = 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_of_equiv_alt6 e]
  omega

end LemmaK

section Restrict

variable {N X : Type*} [Group N]

@[expose] def restrictAct (ρ : N →* Perm X) (O : Set X) (hO : ∀ n, ∀ x ∈ O, ρ n x ∈ O) :
    N →* Perm O where
  toFun n := (ρ n).subtypePerm (fun x => ⟨fun hx => by
    have := hO n⁻¹ _ hx
    simpa [map_inv, Equiv.Perm.inv_def] using this, hO n x⟩)
  map_one' := Equiv.ext fun x => Subtype.ext (by simp)
  map_mul' a b := Equiv.ext fun x => Subtype.ext (by
    show ρ (a * b) x = ρ a (ρ b x)
    rw [map_mul]; rfl)

end Restrict

section Orbits

variable {G : Type*} [Group G] {P : Type*} (ρ : G →* Perm P) (L : Subgroup G)

@[expose] def orb (x : P) : Set P := {z | ∃ g ∈ L, ρ g x = z}

variable {ρ L}

theorem mem_orb_self (x : P) : x ∈ orb ρ L x := ⟨1, L.one_mem, by simp⟩

theorem orb_eq_of_mem {x z : P} (hz : z ∈ orb ρ L x) : orb ρ L z = orb ρ L x := by
  obtain ⟨g, hg, rfl⟩ := hz
  ext w
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g, L.mul_mem hh hg, by simp⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h * g⁻¹, L.mul_mem hh (L.inv_mem hg), by simp [map_mul, map_inv, Equiv.Perm.inv_def]⟩

theorem image_orb_of_mem_normalizer {n : G} (hn : n ∈ normalizer (L : Set G)) (x : P) :
    ρ n '' orb ρ L x = orb ρ L (ρ n x) := by
  ext w
  constructor
  · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨n * g * n⁻¹, (mem_normalizer_iff.mp hn g).mp hg, ?_⟩
    simp [map_mul, map_inv, Equiv.Perm.inv_def]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨ρ (n⁻¹ * g * n) x, ⟨n⁻¹ * g * n, ?_, rfl⟩, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hn) g).mp hg
      simpa using this
    · simp [map_mul, map_inv, Equiv.Perm.inv_def]

end Orbits

section Main

open CFSG.QuasithinUnique.Setup.X5

variable {G : Type*} [Group G] {P : Type*} [Fintype P] (ρ : G →* Perm P) (L : Subgroup G)

open scoped Classical in
theorem six_point_abstract [Group.IsPerfect L]
    (eQ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6))
    (hZ : ∀ g : L, g ∈ Subgroup.center L → ρ g = 1)
    {x y : P} (hx : (orb ρ L x).ncard = 6) (hy : (orb ρ L y).ncard = 15)
    (hcov : ∀ z, z ∈ orb ρ L x ∨ z ∈ orb ρ L y) :
    ∃ θ : normalizer (L : Set G) →* Perm (orb ρ L x),
      (∀ n z, (θ n z : P) = ρ n z) ∧
      (∀ n, θ n = 1 → (n : G) ∈ Subgroup.centralizer (L : Set G)) ∧
      (L.subgroupOf (normalizer (L : Set G))).map θ = alternatingGroup (orb ρ L x) := by
  have hinv : ∀ n : G, n ∈ normalizer (L : Set G) → ∀ z ∈ orb ρ L x, ρ n z ∈ orb ρ L x := by
    intro n hn z hz
    have himg := image_orb_of_mem_normalizer (ρ := ρ) (L := L) hn x
    have hcard : (orb ρ L (ρ n x)).ncard = 6 := by
      rw [← himg, Set.ncard_image_of_injective _ (ρ n).injective, hx]
    rcases hcov (ρ n x) with h | h
    · have h1 := orb_eq_of_mem h
      rw [← himg] at h1
      have h2 : ρ n z ∈ ρ n '' orb ρ L x := ⟨z, hz, rfl⟩
      rwa [h1] at h2
    · exfalso
      have h1 := orb_eq_of_mem h
      rw [h1, hy] at hcard
      omega
  let θ : normalizer (L : Set G) →* Perm (orb ρ L x) :=
    restrictAct (ρ.comp (normalizer (L : Set G)).subtype) (orb ρ L x)
      (fun n z hz => hinv n.1 n.2 z hz)
  have hθ : ∀ (n : normalizer (L : Set G)) (z : orb ρ L x), (θ n z : P) = ρ n z := fun n z => rfl
  have hLN : L ≤ normalizer (L : Set G) := Subgroup.le_normalizer
  let θL : L →* Perm (orb ρ L x) := θ.comp (Subgroup.inclusion hLN)
  have hθL : ∀ (g : L) (z : orb ρ L x), (θL g z : P) = ρ g z := fun g z => rfl
  have hcenter : Subgroup.center L ≤ θL.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    ext z
    have := hZ g hg
    rw [hθL, this]
    rfl
  let ψ : (L ⧸ Subgroup.center L) →* Perm (orb ρ L x) := QuotientGroup.lift _ θL hcenter
  have hψ : ∀ (g : L), ψ (QuotientGroup.mk g) = θL g := fun g => rfl
  have hcard : Fintype.card (orb ρ L x) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hx]
  have hψne : ψ ≠ 1 := by
    intro h1
    have hall : ∀ g : L, ρ g x = x := by
      intro g
      have := congrArg (fun m : Perm (orb ρ L x) => (m ⟨x, mem_orb_self x⟩ : P))
        (show ψ (QuotientGroup.mk g) = 1 by rw [h1]; rfl)
      simpa [hψ, hθL] using this
    have hsub : orb ρ L x ⊆ {x} := by
      rintro z ⟨g, hg, rfl⟩
      exact hall ⟨g, hg⟩
    have := Set.ncard_le_ncard hsub (Set.finite_singleton x)
    rw [Set.ncard_singleton, hx] at this
    omega
  obtain ⟨hψinj, hψrange⟩ := injective_and_range_alt eQ ψ hcard hψne
  refine ⟨θ, hθ, ?_, ?_⟩
  · intro n hn
    have hact : normalizerAct L n = 1 := by
      ext q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAut.one_apply, normalizerAct_apply_mk]
      apply hψinj
      rw [hψ, hψ]
      ext z
      have hn1 : ∀ w : orb ρ L x, ρ n w = w := fun w => by
        have := congrArg (fun m : Perm (orb ρ L x) => (m w : P)) hn
        simpa [hθ] using this
      have hn2 : ∀ w : orb ρ L x, ρ (n : G)⁻¹ w = w := fun w => by
        have := hn1 w
        calc ρ (n : G)⁻¹ w = ρ (n : G)⁻¹ (ρ n w) := by rw [this]
          _ = w := by simp [map_inv, Equiv.Perm.inv_def]
      rw [hθL, hθL]
      show ρ (n * l * n⁻¹ : G) z = ρ l z
      have hlz : ρ l z ∈ orb ρ L x := by
        obtain ⟨g, hg, hz⟩ := z.2
        exact ⟨l * g, L.mul_mem l.2 hg, by rw [map_mul, Perm.mul_apply, hz]⟩
      calc ρ (n * l * n⁻¹ : G) z = ρ n (ρ l (ρ n⁻¹ z)) := by simp [map_mul]
        _ = ρ n (ρ l z) := by rw [hn2 z]
        _ = ρ l z := hn1 ⟨_, hlz⟩
    exact mem_centralizer_of_normalizerAct_eq_one L hact
  · rw [← hψrange]
    ext σ
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨QuotientGroup.mk ⟨n.1, hn⟩, ?_⟩
      rw [hψ]
      rfl
    · rintro ⟨q, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨⟨l.1, hLN l.2⟩, l.2, rfl⟩

end Main

section Overgroups

variable {N : Type*} [Group N] {O : Type*} [Fintype O] [DecidableEq O]

theorem overgroup_cases (hO : Fintype.card O = 6) (θ : N →* Perm O) (L₀ : Subgroup N)
    (h : L₀.map θ = alternatingGroup O) (K : Subgroup N) (hK : L₀ ≤ K) :
    Nonempty ((K ⧸ (θ.comp K.subtype).ker) ≃* alternatingGroup O) ∨
      Nonempty ((K ⧸ (θ.comp K.subtype).ker) ≃* Perm O) := by
  have hge : alternatingGroup O ≤ (θ.comp K.subtype).range := by
    rw [← h]
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨⟨l, hK hl⟩, rfl⟩
  have hnt : Nontrivial O := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hO]; norm_num
  have hcalt : Nat.card (alternatingGroup O) = 360 := by
    have h1 := two_mul_nat_card_alternatingGroup (α := O)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := O), hO] at h1
    have h720 : (6 : ℕ).factorial = 720 := by decide
    rw [h720] at h1
    omega
  have hcperm : Nat.card (Perm O) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := O), hO]
    decide
  have hd1 : Nat.card (alternatingGroup O) ∣ Nat.card (θ.comp K.subtype).range :=
    Subgroup.card_dvd_of_le hge
  have hd2 : Nat.card (θ.comp K.subtype).range ∣ Nat.card (Perm O) :=
    Subgroup.card_subgroup_dvd_card _
  rw [hcalt] at hd1
  rw [hcperm] at hd2
  obtain ⟨c, hc⟩ := hd1
  have hc2 : c ∣ 2 := by
    have h1 : 360 * c ∣ 360 * 2 := hc ▸ hd2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hc2 with h1 | h2
  · left
    have hcard : Nat.card (θ.comp K.subtype).range = 360 := by omega
    have heq : alternatingGroup O = (θ.comp K.subtype).range :=
      Subgroup.eq_of_le_of_card_ge hge (by rw [hcard, hcalt])
    exact ⟨(QuotientGroup.quotientKerEquivRange (θ.comp K.subtype)).trans
      (MulEquiv.subgroupCongr heq.symm)⟩
  · right
    have hcard : Nat.card (θ.comp K.subtype).range = Nat.card (Perm O) := by omega
    have heq : (θ.comp K.subtype).range = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
    exact ⟨(QuotientGroup.quotientKerEquivRange (θ.comp K.subtype)).trans
      ((MulEquiv.subgroupCongr heq).trans Subgroup.topEquiv)⟩

end Overgroups

end CFSG.QuasithinUnique.Setup.X3
