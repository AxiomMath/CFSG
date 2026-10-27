module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecShape3Basic
public import CFSG.LocalAnalysis.OddStandard.AltStdBalSigma

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

omit [Finite G] in
theorem card_roots_conj {R : Subgroup G} {x : G} (hx : ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hx' : ∀ r ∈ R, x⁻¹ * r * x ∈ R) (a : G) :
    Nat.card {r : R // (r : G) ^ 2 = a} = Nat.card {r : R // (r : G) ^ 2 = x * a * x⁻¹} := by
  refine Nat.card_congr
    { toFun := fun r => ⟨⟨x * r * x⁻¹, hx r r.1.2⟩, ?_⟩
      invFun := fun r => ⟨⟨x⁻¹ * r * x, hx' r r.1.2⟩, ?_⟩
      left_inv := fun r => ?_
      right_inv := fun r => ?_ }
  · have := r.2
    calc ((x * (r.1 : G) * x⁻¹) ^ 2) = x * (r.1 : G) ^ 2 * x⁻¹ := by rw [sq, sq]; group
      _ = x * a * x⁻¹ := by rw [this]
  · have := r.2
    calc ((x⁻¹ * (r.1 : G) * x) ^ 2) = x⁻¹ * (r.1 : G) ^ 2 * x := by rw [sq, sq]; group
      _ = a := by rw [this]; group
  · apply Subtype.ext; apply Subtype.ext; simp [mul_assoc]
  · apply Subtype.ext; apply Subtype.ext; simp [mul_assoc]

theorem card_subtype_comp {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (p : B → Prop) :
    Nat.card {a : A // p (f a)} = Nat.card f.ker * Nat.card {b : B // p b} := by
  classical
  let σ : B → A := Function.surjInv hf
  have hσ : ∀ b, f (σ b) = b := Function.surjInv_eq hf
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun a => (⟨a.1 * (σ (f a.1))⁻¹, by simp [MonoidHom.mem_ker, hσ]⟩, ⟨f a.1, a.2⟩)
      invFun := fun kb => ⟨kb.1.1 * σ kb.2.1, by
        rw [map_mul, hσ, MonoidHom.mem_ker.1 kb.1.2, one_mul]
        exact kb.2.2⟩
      left_inv := fun a => by
        apply Subtype.ext
        simp
      right_inv := fun kb => by
        have hfb : f (kb.1.1 * σ kb.2.1) = kb.2.1 := by
          rw [map_mul, hσ, MonoidHom.mem_ker.1 kb.1.2, one_mul]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simp only [hfb]
          simp
        · simpa using hfb }

section Transport

variable (e : L ≃* alternatingGroup (Fin n))

@[expose] noncomputable def rhoR (h : Setting G L n) (d : Cyc L Q z) (R : Subgroup G)
    (hRC : R ≤ centralizer ({z} : Set G)) : R →* Perm (Fin n) :=
  (rho e h.hn).comp (Subgroup.inclusion (hRC.trans (AltStdBal.centralizer_le_normalizer h d)))

theorem rhoR_apply (h : Setting G L n) (d : Cyc L Q z) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (r : R) :
    rhoR e h d R hRC r = rho e h.hn ⟨r, AltStdBal.centralizer_le_normalizer h d (hRC r.2)⟩ := by
  rfl

theorem rhoR_ker_card (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (hzR : z ∈ R) :
    Nat.card (rhoR e h d R hRC).ker = 2 := by
  have hz1 : z ≠ 1 := by
    intro h1
    have := d.order
    rw [h1, orderOf_one] at this
    omega
  have hkerz : (⟨z, hzR⟩ : R) ∈ (rhoR e h d R hRC).ker := by
    rw [MonoidHom.mem_ker, rhoR_apply]
    exact (rho_eq_one_iff e h.hn _).2 (d.le d.mem)
  rw [Nat.card_eq_two_iff' (1 : (rhoR e h d R hRC).ker)]
  refine ⟨⟨⟨z, hzR⟩, hkerz⟩, ?_, ?_⟩
  · intro h1
    have := congrArg (fun y : (rhoR e h d R hRC).ker => ((y : R) : G)) h1
    exact hz1 (by simpa using this)
  · intro y hy
    have hy1 : rhoR e h d R hRC y = 1 := y.2
    rw [rhoR_apply] at hy1
    have hyK := (rho_eq_one_iff e h.hn _).1 hy1
    have hyQ : ((y : R) : G) ∈ Q := by
      have hmem : ((y : R) : G) ∈ centralizer (L : Set G) ⊓ centralizer ({z} : Set G) :=
        ⟨hyK, hRC (y : R).2⟩
      rwa [cent_inf_eq h d] at hmem
    rcases eq_one_or_eq_of_card_eq_two d hQ2 hyQ with h2 | h2
    · exfalso
      apply hy
      apply Subtype.ext
      apply Subtype.ext
      simpa using h2
    · apply Subtype.ext
      apply Subtype.ext
      simpa using h2

theorem sign_rhoR_eq_neg_one_iff (h : Setting G L n) (d : Cyc L Q z) {R : Subgroup G}
    (hRC : R ≤ centralizer ({z} : Set G)) (r : R) :
    Perm.sign (rhoR e h d R hRC r) = -1 ↔ (r : G) ∉ L ⊔ Q := by
  have h1 := mem_sup_iff h d e (hRC r.2)
  have h2 : signHom e h.hn ⟨(r : G), AltStdBal.centralizer_le_normalizer h d (hRC r.2)⟩ =
      Perm.sign (rhoR e h d R hRC r) := rfl
  rw [h2] at h1
  constructor
  · intro hs hmem
    have := h1.1 hmem
    rw [hs] at this
    exact absurd this (by decide)
  · intro hnot
    rcases Int.units_eq_one_or (Perm.sign (rhoR e h d R hRC r)) with h3 | h3
    · exact absurd (h1.2 h3) hnot
    · exact h3

theorem sq_eq_iff (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = z)
    {R : Subgroup G} (hRC : R ≤ centralizer ({z} : Set G)) (w : L) (r : R) :
    (r : G) ^ 2 = z * (w : G) ↔
      (Perm.sign (rhoR e h d R hRC r) = -1 ∧
        (rhoR e h d R hRC r) ^ 2 = ((e w : alternatingGroup (Fin n)) : Perm (Fin n))) := by
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hzN : z ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d hzC
  have hρz : rho e h.hn ⟨z, hzN⟩ = 1 := (rho_eq_one_iff e h.hn _).2 (d.le d.mem)
  have hwN : (w : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer w.2
  have hρw : rho e h.hn ⟨(w : G), hwN⟩ = ((e w : alternatingGroup (Fin n)) : Perm (Fin n)) :=
    rho_of_mem e h.hn w hwN
  have hrN : (r : G) ∈ normalizer (L : Set G) :=
    AltStdBal.centralizer_le_normalizer h d (hRC r.2)
  have hsq : (rhoR e h d R hRC r) ^ 2 =
      rho e h.hn ⟨(r : G) * (r : G), mul_mem hrN hrN⟩ := by
    rw [sq, ← map_mul]
    rfl
  constructor
  · intro hr2
    have hrQ : (r : G) ∉ L ⊔ Q := by
      intro hmem
      have h1 := sq_mem_L_of_mem_sup d hQ2 hmem
      rw [hr2] at h1
      apply z_not_mem_L h d
      have : z = (z * (w : G)) * (w : G)⁻¹ := by group
      rw [this]
      exact mul_mem h1 (inv_mem w.2)
    refine ⟨(sign_rhoR_eq_neg_one_iff e h d hRC r).2 hrQ, ?_⟩
    rw [hsq]
    have h2 : (⟨(r : G) * (r : G), mul_mem hrN hrN⟩ : normalizer (L : Set G)) =
        ⟨z, hzN⟩ * ⟨(w : G), hwN⟩ := Subtype.ext (by
          have h7 := hr2
          rw [sq] at h7
          exact h7)
    rw [h2, map_mul, hρz, hρw, one_mul]
  · rintro ⟨hs, hsq2⟩
    have hrQ := (sign_rhoR_eq_neg_one_iff e h d hRC r).1 hs
    obtain ⟨l, hl, hrr⟩ := sq_mem_mul_L_of_outer h d hQ2 hu huL hu2 (hRC r.2) hrQ
    have hlN : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hl
    have h3 : rho e h.hn ⟨l, hlN⟩ = ((e ⟨l, hl⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
      rho_of_mem e h.hn ⟨l, hl⟩ hlN
    have h4 : (⟨(r : G) * (r : G), mul_mem hrN hrN⟩ : normalizer (L : Set G)) =
        ⟨z, hzN⟩ * ⟨l, hlN⟩ := Subtype.ext hrr
    rw [hsq, h4, map_mul, hρz, one_mul, h3] at hsq2
    have h5 : (⟨l, hl⟩ : L) = w := e.injective (Subtype.ext hsq2)
    have h6 : l = (w : G) := congrArg Subtype.val h5
    rw [sq, hrr, h6]

theorem card_roots_eq_two_mul (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = z)
    {R : Subgroup G} (hRC : R ≤ centralizer ({z} : Set G)) (hzR : z ∈ R) (w : L) :
    Nat.card {r : R // (r : G) ^ 2 = z * (w : G)} =
      2 * Nat.card {s : (rhoR e h d R hRC).range //
        Perm.sign (s : Perm (Fin n)) = -1 ∧
          (s : Perm (Fin n)) ^ 2 = ((e w : alternatingGroup (Fin n)) : Perm (Fin n))} := by
  have hπ : Function.Surjective (rhoR e h d R hRC).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have key := card_subtype_comp (rhoR e h d R hRC).rangeRestrict hπ
    (fun s => Perm.sign (s : Perm (Fin n)) = -1 ∧
      (s : Perm (Fin n)) ^ 2 = ((e w : alternatingGroup (Fin n)) : Perm (Fin n)))
  rw [MonoidHom.ker_rangeRestrict, rhoR_ker_card e h d hQ2 hRC hzR] at key
  rw [← key]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight (fun r => sq_eq_iff e h d hQ2 hu huL hu2 hRC w r))

theorem rhoC_surjective (h : Setting G L n) (d : Cyc L Q z) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) :
    Function.Surjective (rhoR e h d (centralizer ({z} : Set G)) le_rfl) := by
  intro σ
  have hsu : Perm.sign (rhoR e h d (centralizer ({z} : Set G)) le_rfl ⟨u, hu⟩) = -1 :=
    (sign_rhoR_eq_neg_one_iff e h d le_rfl ⟨u, hu⟩).2 huL
  have heven : ∀ τ : Perm (Fin n), Perm.sign τ = 1 →
      ∃ c : centralizer ({z} : Set G),
        rhoR e h d (centralizer ({z} : Set G)) le_rfl c = τ := by
    intro τ hτ
    have hmem : τ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hτ
    let l : L := e.symm ⟨τ, hmem⟩
    refine ⟨⟨l, le_centralizer_single h d l.2⟩, ?_⟩
    rw [rhoR_apply, rho_of_mem e h.hn l (AltStdBal.centralizer_le_normalizer h d
      (le_centralizer_single h d l.2))]
    simp [l]
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
  · exact heven σ hs
  · obtain ⟨c, hc⟩ := heven ((rhoR e h d (centralizer ({z} : Set G)) le_rfl ⟨u, hu⟩)⁻¹ * σ)
      (by rw [map_mul, map_inv, hsu, hs]; decide)
    refine ⟨⟨u, hu⟩ * c, ?_⟩
    rw [map_mul, hc]
    group

theorem range_rhoR_maximal (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q)
    {R : Subgroup G} (hRC : R ≤ centralizer ({z} : Set G)) (hR : IsPGroup 2 R)
    (hRmax : ∀ R' : Subgroup G, R' ≤ centralizer ({z} : Set G) → IsPGroup 2 R' → R ≤ R' →
      R' = R) :
    IsPGroup 2 (rhoR e h d R hRC).range ∧
      ∀ P' : Subgroup (Perm (Fin n)), IsPGroup 2 P' → (rhoR e h d R hRC).range ≤ P' →
        P' = (rhoR e h d R hRC).range := by
  have hπ := MonoidHom.rangeRestrict_surjective (rhoR e h d R hRC)
  refine ⟨hR.of_surjective _ hπ, ?_⟩
  intro P' hP' hle
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hker : IsPGroup 2 (rhoR e h d (centralizer ({z} : Set G)) le_rfl).ker :=
    IsPGroup.of_card (n := 1) (by rw [rhoR_ker_card e h d hQ2 le_rfl hzC]; norm_num)
  let R'' : Subgroup G :=
    (P'.comap (rhoR e h d (centralizer ({z} : Set G)) le_rfl)).map
      (centralizer ({z} : Set G)).subtype
  have hR''C : R'' ≤ centralizer ({z} : Set G) := Subgroup.map_subtype_le _
  have hR''p : IsPGroup 2 R'' :=
    (hP'.comap_of_ker_isPGroup _ hker).map (centralizer ({z} : Set G)).subtype
  have hRR'' : R ≤ R'' := by
    intro r hr
    refine ⟨⟨r, hRC hr⟩, ?_, rfl⟩
    show rhoR e h d (centralizer ({z} : Set G)) le_rfl ⟨r, hRC hr⟩ ∈ P'
    exact hle ⟨⟨r, hr⟩, rfl⟩
  have hEq : R'' = R := hRmax R'' hR''C hR''p hRR''
  refine le_antisymm ?_ hle
  intro s hs
  obtain ⟨c, hc⟩ := rhoC_surjective e h d hu huL s
  have hcR'' : (c : G) ∈ R'' := ⟨c, by
    show rhoR e h d (centralizer ({z} : Set G)) le_rfl c ∈ P'
    rw [hc]
    exact hs, rfl⟩
  rw [hEq] at hcR''
  exact ⟨⟨c, hcR''⟩, by rw [← hc]; rfl⟩

end Transport

end CFSG.OddStandard.AltStdSec
