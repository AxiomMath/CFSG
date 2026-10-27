module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type} [Group G]

@[expose] def cjAut (P : Subgroup G) (n : ↥(normalizer (P : Set G))) : MulAut ↥P where
  toFun p := ⟨(n : G) * p * (n : G)⁻¹, (mem_normalizer_iff.1 n.2 p).1 p.2⟩
  invFun p := ⟨(n : G)⁻¹ * p * (n : G), (mem_normalizer_iff.1 n.2 _).2 (by
    have e : (n : G) * ((n : G)⁻¹ * p * (n : G)) * (n : G)⁻¹ = p := by group
    rw [e]; exact p.2)⟩
  left_inv p := Subtype.ext (by group)
  right_inv p := Subtype.ext (by group)
  map_mul' a b := Subtype.ext (by
    show (n : G) * ((a : G) * (b : G)) * (n : G)⁻¹ =
      ((n : G) * a * (n : G)⁻¹) * ((n : G) * b * (n : G)⁻¹)
    group)

@[expose] def actHom (P : Subgroup G) : ↥(normalizer (P : Set G)) →* MulAut ↥P where
  toFun := cjAut P
  map_one' := by
    ext p
    show (1 : G) * p * (1 : G)⁻¹ = p
    group
  map_mul' a b := by
    ext p
    show (a : G) * (b : G) * p * ((a : G) * (b : G))⁻¹ = (a : G) * ((b : G) * p * (b : G)⁻¹) * (a : G)⁻¹
    group

theorem actHom_of_mem {P : Subgroup G} (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (n : ↥(normalizer (P : Set G))) (hn : (n : G) ∈ P) : actHom P n = 1 := by
  ext p
  show (n : G) * p * (n : G)⁻¹ = p
  have := hP _ hn p p.2
  calc (n : G) * p * (n : G)⁻¹ = (p * (n : G)) * (n : G)⁻¹ := by rw [this]
    _ = p := by group

theorem actHom_eq_one_iff {P : Subgroup G} (n : ↥(normalizer (P : Set G))) :
    actHom P n = 1 ↔ ∀ p ∈ P, (n : G) * p * (n : G)⁻¹ = p := by
  constructor
  · intro h p hp
    have := congrArg (fun m : MulAut ↥P => ((m ⟨p, hp⟩ : ↥P) : G)) h
    exact this
  · intro h
    ext p
    exact h p p.2

@[expose] def imgS (P S : Subgroup G) : Subgroup (MulAut ↥P) :=
  (S.subgroupOf (normalizer (P : Set G))).map (actHom P)

theorem mem_imgS {P S : Subgroup G} {σ : MulAut ↥P} :
    σ ∈ imgS P S ↔ ∃ s ∈ S, ∃ hs : s ∈ normalizer (P : Set G), actHom P ⟨s, hs⟩ = σ := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.1, hn, n.2, rfl⟩
  · rintro ⟨s, hs, hsN, rfl⟩
    exact ⟨⟨s, hsN⟩, hs, rfl⟩

theorem imgS_le_range (P S : Subgroup G) : imgS P S ≤ (actHom P).range :=
  Subgroup.map_le_range _ _

theorem sylow2In_imgS [Finite G] {P S : Subgroup G} (hS : Sylow2In S ⊤)
    (hSN : S ≤ normalizer (P : Set G)) : Sylow2In (imgS P S) (actHom P).range := by
  refine ⟨imgS_le_range P S, ?_, ?_⟩
  · have h1 : IsPGroup 2 ↥(S.subgroupOf (normalizer (P : Set G))) :=
      hS.2.1.of_equiv (subgroupOfEquivOfLe hSN).symm
    exact h1.map (actHom P)
  · intro hdvd
    apply hS.2.2
    set φ' := (actHom P).rangeRestrict with hφ'
    have hsurj : Function.Surjective φ' := (actHom P).rangeRestrict_surjective
    have hsub : (imgS P S).subgroupOf (actHom P).range =
        (S.subgroupOf (normalizer (P : Set G))).map φ' := by
      ext y
      rw [mem_subgroupOf]
      constructor
      · intro hy
        obtain ⟨n, hn, hny⟩ := hy
        exact ⟨n, hn, Subtype.ext hny⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
    have h1 : ((S.subgroupOf (normalizer (P : Set G))).map φ').index ∣
        (S.subgroupOf (normalizer (P : Set G))).index :=
      Subgroup.index_map_dvd _ hsurj
    have h2 : (S.subgroupOf (normalizer (P : Set G))).index ∣ S.relIndex ⊤ := by
      rw [relIndex_top_right]
      exact relIndex_dvd_index_of_le hSN
    have h3 : (imgS P S).relIndex (actHom P).range ∣ S.relIndex ⊤ := by
      show ((imgS P S).subgroupOf (actHom P).range).index ∣ S.relIndex ⊤
      rw [hsub]
      exact h1.trans h2
    exact hdvd.trans h3

section Rho

open Classical in
@[expose] noncomputable def rho (P : Subgroup G) (s : G) : MulAut ↥P :=
  if h : s ∈ normalizer (P : Set G) then actHom P ⟨s, h⟩ else 1

variable {P : Subgroup G}

theorem rho_of_mem {s : G} (h : s ∈ normalizer (P : Set G)) : rho P s = actHom P ⟨s, h⟩ :=
  by simp [rho, h]

theorem rho_apply {s : G} (h : s ∈ normalizer (P : Set G)) (p : ↥P) :
    ((rho P s p : ↥P) : G) = s * p * s⁻¹ := by
  rw [rho_of_mem h]; rfl

theorem rho_mul {s s' : G} (hs : s ∈ normalizer (P : Set G)) (hs' : s' ∈ normalizer (P : Set G)) :
    rho P (s * s') = rho P s * rho P s' := by
  rw [rho_of_mem hs, rho_of_mem hs', rho_of_mem ((normalizer (P : Set G)).mul_mem hs hs'),
    ← map_mul]
  rfl

theorem rho_one : rho P 1 = 1 := by
  rw [rho_of_mem (one_mem _)]
  exact map_one _

theorem rho_eq_one_iff {s : G} (h : s ∈ normalizer (P : Set G)) :
    rho P s = 1 ↔ ∀ p ∈ P, s * p * s⁻¹ = p := by
  rw [rho_of_mem h]
  exact actHom_eq_one_iff _

theorem rho_of_mem_P (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {s : G} (hs : s ∈ P) : rho P s = 1 := by
  rw [rho_of_mem (Subgroup.le_normalizer hs)]
  exact actHom_of_mem hP _ hs

theorem rho_eq_of_quot (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {s s' : G}
    (hs : s ∈ normalizer (P : Set G)) (hs' : s' ∈ normalizer (P : Set G)) (h : s⁻¹ * s' ∈ P) :
    rho P s = rho P s' := by
  have hs'e : s' = s * (s⁻¹ * s') := by group
  rw [hs'e, rho_mul hs ((normalizer (P : Set G)).mul_mem ((normalizer (P : Set G)).inv_mem hs) hs'),
    rho_of_mem_P hP h, mul_one]

theorem mem_imgS_rho {S : Subgroup G} {σ : MulAut ↥P} :
    σ ∈ imgS P S ↔ ∃ s ∈ S, s ∈ normalizer (P : Set G) ∧ rho P s = σ := by
  rw [mem_imgS]
  constructor
  · rintro ⟨s, hs, hsN, h⟩
    exact ⟨s, hs, hsN, by rw [rho_of_mem hsN]; exact h⟩
  · rintro ⟨s, hs, hsN, h⟩
    exact ⟨s, hs, hsN, by rw [← rho_of_mem hsN]; exact h⟩

end Rho

section RhoPow

variable {P : Subgroup G}

theorem rho_pow {s : G} (hs : s ∈ normalizer (P : Set G)) (n : ℕ) : rho P (s ^ n) = (rho P s) ^ n := by
  induction n with
  | zero => simp [rho_one]
  | succ n ih =>
    rw [pow_succ, rho_mul ((normalizer (P : Set G)).pow_mem hs n) hs, ih, pow_succ]

theorem rho_inv {s : G} (hs : s ∈ normalizer (P : Set G)) : rho P s⁻¹ = (rho P s)⁻¹ := by
  have h := rho_mul hs ((normalizer (P : Set G)).inv_mem hs)
  rw [mul_inv_cancel, rho_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

end RhoPow

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
