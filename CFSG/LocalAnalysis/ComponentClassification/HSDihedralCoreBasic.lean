module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreDefs

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools

variable {X : Type} [Group X] {A : Type} [Group A]

theorem mem_of_isSylowOf_centralizer [Finite X] {t : X} (ht : orderOf t = 2) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) : t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht, pow_one]
  have hle : zpowers t ≤ normalizer (S : Set X) := by
    rw [zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun s hs => ?_)
    exact mem_centralizer_singleton_iff.mp (hS.le hs)
  have hsup : IsPGroup 2 (S ⊔ zpowers t : Subgroup X) :=
    hS.isPGroup.to_sup_of_normal_left' ht2 hle
  have htH : zpowers t ≤ centralizer ({t} : Set X) := by
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr rfl
  have heq := hS.eq_of_le le_sup_left (sup_le hS.le htH) hsup
  rw [← heq]
  exact mem_sup_right (mem_zpowers t)

namespace LocalDatum

variable (Δ : LocalDatum X A)

@[expose] def ψe (x : X) : A := by
  classical
  exact if hx : x ∈ Δ.S then Δ.ψ ⟨x, hx⟩ else 1

theorem ψe_of_mem {x : X} (hx : x ∈ Δ.S) : Δ.ψe x = Δ.ψ ⟨x, hx⟩ := by
  simp [ψe, hx]

theorem ψe_mul {x y : X} (hx : x ∈ Δ.S) (hy : y ∈ Δ.S) : Δ.ψe (x * y) = Δ.ψe x * Δ.ψe y := by
  rw [Δ.ψe_of_mem (mul_mem hx hy), Δ.ψe_of_mem hx, Δ.ψe_of_mem hy, ← map_mul]
  rfl

theorem ψe_inv {x : X} (hx : x ∈ Δ.S) : Δ.ψe x⁻¹ = (Δ.ψe x)⁻¹ := by
  rw [Δ.ψe_of_mem (inv_mem hx), Δ.ψe_of_mem hx, ← map_inv]
  rfl

theorem ψe_one : Δ.ψe 1 = 1 := by
  rw [Δ.ψe_of_mem (one_mem _), ← map_one Δ.ψ]
  rfl

theorem ψe_pow {x : X} (hx : x ∈ Δ.S) (n : ℕ) : Δ.ψe (x ^ n) = Δ.ψe x ^ n := by
  rw [Δ.ψe_of_mem (pow_mem hx n), Δ.ψe_of_mem hx, ← map_pow]
  rfl

theorem ψe_conj {x y : X} (hx : x ∈ Δ.S) (hy : y ∈ Δ.S) :
    Δ.ψe (x * y * x⁻¹) = Δ.ψe x * Δ.ψe y * (Δ.ψe x)⁻¹ := by
  rw [Δ.ψe_mul (mul_mem hx hy) (inv_mem hx), Δ.ψe_mul hx hy, Δ.ψe_inv hx]

theorem mem_R_iff {y : A} : y ∈ Δ.R ↔ ∃ s ∈ Δ.S, Δ.ψe s = y := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.2, Δ.ψe_of_mem s.2⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, (Δ.ψe_of_mem hs).symm⟩

theorem ψe_mem_R {s : X} (hs : s ∈ Δ.S) : Δ.ψe s ∈ Δ.R := (Δ.mem_R_iff).mpr ⟨s, hs, rfl⟩

theorem mem_Dbar_iff {y : A} : y ∈ Δ.Dbar ↔ ∃ d ∈ Δ.D, Δ.ψe d = y := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, Δ.ψe_of_mem s.2⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, Δ.D_le hd⟩, hd, (Δ.ψe_of_mem (Δ.D_le hd)).symm⟩

theorem ψe_mem_Dbar {d : X} (hd : d ∈ Δ.D) : Δ.ψe d ∈ Δ.Dbar :=
  (Δ.mem_Dbar_iff).mpr ⟨d, hd, rfl⟩

theorem mem_Q_iff {x : X} : x ∈ Δ.Q ↔ x ∈ Δ.S ∧ Δ.ψe x = 1 := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    change Δ.ψe (s : X) = 1
    rw [Δ.ψe_of_mem s.2]
    exact hs
  · rintro ⟨hx, h1⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change Δ.ψ ⟨x, hx⟩ = 1
    rw [← Δ.ψe_of_mem hx]
    exact h1

theorem Q_le : Δ.Q ≤ Δ.S := map_subtype_le _

theorem eq_one_of_ψe {d : X} (hd : d ∈ Δ.D) (h1 : Δ.ψe d = 1) : d = 1 :=
  Δ.eq_one_of_mem_D d hd (by rw [← Δ.ψe_of_mem]; exact h1)

theorem eq_of_ψe_eq {d d' : X} (hd : d ∈ Δ.D) (hd' : d' ∈ Δ.D) (h : Δ.ψe d = Δ.ψe d') :
    d = d' := by
  have h1 : Δ.ψe (d * d'⁻¹) = 1 := by
    rw [Δ.ψe_mul (Δ.D_le hd) (inv_mem (Δ.D_le hd')), Δ.ψe_inv (Δ.D_le hd'), h, mul_inv_cancel]
  have := Δ.eq_one_of_ψe (mul_mem hd (inv_mem hd')) h1
  exact mul_inv_eq_one.mp this

theorem t_sq : Δ.t ^ 2 = 1 := by rw [← Δ.orderOf_t, pow_orderOf_eq_one]

theorem t_ne_one : Δ.t ≠ 1 := by
  intro h1
  have := Δ.orderOf_t
  rw [h1, orderOf_one] at this
  norm_num at this

theorem commute_t {s : X} (hs : s ∈ Δ.S) : s * Δ.t = Δ.t * s :=
  mem_centralizer_singleton_iff.mp (Δ.sylow.le hs)

theorem conj_mem_Q {s q : X} (hs : s ∈ Δ.S) (hq : q ∈ Δ.Q) : s * q * s⁻¹ ∈ Δ.Q := by
  obtain ⟨hqS, hq1⟩ := (Δ.mem_Q_iff).mp hq
  refine (Δ.mem_Q_iff).mpr ⟨mul_mem (mul_mem hs hqS) (inv_mem hs), ?_⟩
  rw [Δ.ψe_conj hs hqS, hq1, mul_one, mul_inv_cancel]

theorem commute_of_mem_Q_D {q d : X} (hq : q ∈ Δ.Q) (hd : d ∈ Δ.D) : q * d = d * q := by
  obtain ⟨hqS, hq1⟩ := (Δ.mem_Q_iff).mp hq
  have hc : q * d * q⁻¹ * d⁻¹ ∈ Δ.D := mul_mem (Δ.conj_mem_D q hqS d hd) (inv_mem hd)
  have h1 : Δ.ψe (q * d * q⁻¹ * d⁻¹) = 1 := by
    rw [Δ.ψe_mul (Δ.D_le (Δ.conj_mem_D q hqS d hd)) (inv_mem (Δ.D_le hd)),
      Δ.ψe_conj hqS (Δ.D_le hd), Δ.ψe_inv (Δ.D_le hd), hq1]
    group
  have h2 := Δ.eq_one_of_ψe hc h1
  calc q * d = q * d * q⁻¹ * d⁻¹ * (d * q) := by group
    _ = d * q := by rw [h2, one_mul]

theorem eq_one_of_mem_Q_D {x : X} (hq : x ∈ Δ.Q) (hd : x ∈ Δ.D) : x = 1 :=
  Δ.eq_one_of_ψe hd ((Δ.mem_Q_iff).mp hq).2

theorem commute_iff {s d : X} (hs : s ∈ Δ.S) (hd : d ∈ Δ.D) :
    s * d = d * s ↔ Δ.ψe s * Δ.ψe d = Δ.ψe d * Δ.ψe s := by
  constructor
  · intro hc
    rw [← Δ.ψe_mul hs (Δ.D_le hd), ← Δ.ψe_mul (Δ.D_le hd) hs, hc]
  · intro hc
    have hcD : s * d * s⁻¹ * d⁻¹ ∈ Δ.D := mul_mem (Δ.conj_mem_D s hs d hd) (inv_mem hd)
    have h1 : Δ.ψe (s * d * s⁻¹ * d⁻¹) = 1 := by
      rw [Δ.ψe_mul (Δ.D_le (Δ.conj_mem_D s hs d hd)) (inv_mem (Δ.D_le hd)),
        Δ.ψe_conj hs (Δ.D_le hd), Δ.ψe_inv (Δ.D_le hd), hc]
      group
    have h2 := Δ.eq_one_of_ψe hcD h1
    calc s * d = s * d * s⁻¹ * d⁻¹ * (d * s) := by group
      _ = d * s := by rw [h2, one_mul]

variable [Finite X]

theorem t_mem : Δ.t ∈ Δ.S := mem_of_isSylowOf_centralizer Δ.orderOf_t Δ.sylow

theorem ψe_t : Δ.ψe Δ.t = 1 := by
  rw [Δ.ψe_of_mem Δ.t_mem]
  exact Δ.t_mem_ker Δ.t_mem

theorem t_mem_Q : Δ.t ∈ Δ.Q := (Δ.mem_Q_iff).mpr ⟨Δ.t_mem, Δ.ψe_t⟩

omit [Finite X] in
theorem card_Dbar : Nat.card Δ.Dbar = Nat.card Δ.D := by
  have hinj : Function.Injective (Δ.ψ.comp (Δ.D.subgroupOf Δ.S).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxD : ((x : Δ.S) : X) ∈ Δ.D := x.2
    have := Δ.eq_one_of_mem_D _ hxD hx
    exact Subtype.ext (Subtype.ext this)
  rw [show Δ.Dbar = (Δ.ψ.comp (Δ.D.subgroupOf Δ.S).subtype).range by
      rw [MonoidHom.range_comp, range_subtype],
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (subgroupOfEquivOfLe Δ.D_le).toEquiv

theorem eq_t_of_mem_Q {y : X} (hy : y ∈ Δ.Q) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) : y = Δ.t := by
  classical
  obtain ⟨⟨y', hy'S⟩, hy'k, rfl⟩ := hy
  have htk : (⟨Δ.t, Δ.t_mem⟩ : ↥Δ.S) ∈ Δ.ψ.ker := Δ.t_mem_ker Δ.t_mem
  have hc := Δ.isCyclic_ker
  have : Fintype ↥Δ.ψ.ker := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥Δ.ψ.ker) (n := 2) two_pos
  by_contra hne
  have h3 : ({1, ⟨⟨y', hy'S⟩, hy'k⟩, ⟨⟨Δ.t, Δ.t_mem⟩, htk⟩} : Finset ↥Δ.ψ.ker) ⊆
      Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (Subtype.ext hy2)
    · exact Subtype.ext (Subtype.ext Δ.t_sq)
  have h4 := Finset.card_le_card h3
  rw [Finset.card_insert_of_notMem, Finset.card_pair] at h4
  · omega
  · intro h'
    exact hne (congrArg (fun a : ↥Δ.ψ.ker => ((a : ↥Δ.S) : X)) h')
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h' => hy1 ?_, fun h' => Δ.t_ne_one ?_⟩
    · exact (congrArg (fun a : ↥Δ.ψ.ker => ((a : ↥Δ.S) : X)) h').symm
    · exact (congrArg (fun a : ↥Δ.ψ.ker => ((a : ↥Δ.S) : X)) h').symm

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
