module

public import CFSG.ClassicalInvolution.Q3.Q3TIYOAGrp

public section

namespace CFSG.ClassicalInvolution.Q3.GlueLie

open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3TIY
open scoped commutatorElement

section Basic

variable {Q : Type} [Group Q]

theorem le_normalizer_of_forall_conj_mem {M S : Subgroup Q}
    (h : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S) : M ≤ Subgroup.normalizer (S : Set Q) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => h m hm s hs, fun hs => ?_⟩
  have := h m⁻¹ (M.inv_mem hm) _ hs
  simpa [mul_assoc] using this

variable [Finite Q]

theorem eq_one_of_mem_oddCoreIn_of_mul_self {H : Subgroup Q} {x : Q} (hx : x ∈ oddCoreIn H)
    (h2 : x * x = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card (oddCoreIn H) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : oddCoreIn H)
    rwa [Subgroup.orderOf_mk] at this
  have hodd : Odd (orderOf x) := (odd_card_oddCoreIn H).of_dvd_nat h1
  have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

omit [Finite Q] in
theorem exists_pow_mul_mem_oddCoreIn {C : Subgroup Q} {e o : Q} (he : e ∈ C)
    (ho : o ∈ oddCoreIn C) (j : ℕ) : ∃ w ∈ oddCoreIn C, (e * o) ^ j = e ^ j * w := by
  induction j with
  | zero => exact ⟨1, (oddCoreIn C).one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨w, hw, hwj⟩ := ih
    have hw' : e⁻¹ * w * e ∈ oddCoreIn C := by
      have := conj_mem_oddCoreIn (C.inv_mem he) hw
      simpa using this
    refine ⟨(e⁻¹ * w * e) * o, (oddCoreIn C).mul_mem hw' ho, ?_⟩
    rw [pow_succ, hwj, pow_succ]
    group

theorem apply_mem_oddCoreIn_of_map_eq (σ : MulAut Q) {H : Subgroup Q}
    (hH : H.map σ.toMonoidHom = H) {x : Q} (hx : x ∈ oddCoreIn H) : σ x ∈ oddCoreIn H := by
  set S : Subgroup Q := (oddCoreIn H).map σ.toMonoidHom with hS
  have hSH : S ≤ H := by
    rw [← hH]
    exact Subgroup.map_mono (oddCoreIn_le H)
  have hnorm : H ≤ Subgroup.normalizer (S : Set Q) := by
    refine le_normalizer_of_forall_conj_mem fun g hg s hs => ?_
    obtain ⟨o, ho, rfl⟩ := hs
    have hg' : g ∈ H.map σ.toMonoidHom := hH.symm ▸ hg
    obtain ⟨g', hg'H, rfl⟩ := hg'
    exact ⟨g' * o * g'⁻¹, conj_mem_oddCoreIn hg'H ho, by simp⟩
  have hodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective]
    exact odd_card_oddCoreIn H
  exact le_oddCoreIn_of_normalizes hSH hnorm hodd ⟨x, hx, rfl⟩

theorem map_centralizer_of_apply_eq (β : MulAut Q) {z : Q} (hβz : β z = z) :
    (Subgroup.centralizer ({z} : Set Q)).map β.toMonoidHom =
      Subgroup.centralizer ({z} : Set Q) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    show β w * z = z * β w
    rw [← hβz, ← map_mul, hw', map_mul]
  · rw [Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective]

end Basic

section Facts

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem conj_mul_comm_of_mk {c z w : Q}
    (hc : QuotientGroup.mk' (Subgroup.center Q) c * QuotientGroup.mk' (Subgroup.center Q) z =
      QuotientGroup.mk' (Subgroup.center Q) z * QuotientGroup.mk' (Subgroup.center Q) c)
    (hw : w * z = z * w) : (c * w * c⁻¹) * z = z * (c * w * c⁻¹) := by
  have hζc := central_of_mk_commute hc
  set ζ : Q := z⁻¹ * (c * z * c⁻¹) with hζdef
  have hζ : c * z * c⁻¹ = z * ζ := by rw [hζdef]; group
  have hζcomm : ∀ g : Q, g * ζ = ζ * g := Subgroup.mem_center_iff.mp hζc
  have h1 : (c * w * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * w * c⁻¹) := by
    calc (c * w * c⁻¹) * (c * z * c⁻¹) = c * (w * z) * c⁻¹ := by group
      _ = c * (z * w) * c⁻¹ := by rw [hw]
      _ = (c * z * c⁻¹) * (c * w * c⁻¹) := by group
  rw [hζ] at h1
  have h2 : (c * w * c⁻¹) * z * ζ = z * (c * w * c⁻¹) * ζ := by
    calc (c * w * c⁻¹) * z * ζ = (c * w * c⁻¹) * (z * ζ) := by simp only [mul_assoc]
      _ = (z * ζ) * (c * w * c⁻¹) := h1
      _ = z * (ζ * (c * w * c⁻¹)) := by simp only [mul_assoc]
      _ = z * ((c * w * c⁻¹) * ζ) := by rw [hζcomm (c * w * c⁻¹)]
      _ = z * (c * w * c⁻¹) * ζ := by simp only [mul_assoc]
  exact mul_right_cancel h2

theorem map_conj_centralizer_of_mk {c z : Q}
    (hc : QuotientGroup.mk' (Subgroup.center Q) c * QuotientGroup.mk' (Subgroup.center Q) z =
      QuotientGroup.mk' (Subgroup.center Q) z * QuotientGroup.mk' (Subgroup.center Q) c) :
    (Subgroup.centralizer ({z} : Set Q)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({z} : Set Q) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact conj_mul_comm_of_mk hc hw'
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).injective]

omit [Finite Q] in
theorem mk_commute_inv {c z : Q}
    (hc : QuotientGroup.mk' (Subgroup.center Q) c * QuotientGroup.mk' (Subgroup.center Q) z =
      QuotientGroup.mk' (Subgroup.center Q) z * QuotientGroup.mk' (Subgroup.center Q) c) :
    QuotientGroup.mk' (Subgroup.center Q) c⁻¹ * QuotientGroup.mk' (Subgroup.center Q) z =
      QuotientGroup.mk' (Subgroup.center Q) z * QuotientGroup.mk' (Subgroup.center Q) c⁻¹ := by
  rw [map_inv]
  exact ((Commute.inv_left hc) : _)

variable (β : MulAut Q) {z : Q} (hz : z * z = 1)
  (hfix : ∀ c : Q, c * z = z * c → c⁻¹ * β c ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Q)))
include hz hfix

theorem apply_eq_of_mod : β z = z := by
  set o : Q := z⁻¹ * β z with ho
  have hoO : o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Q)) := hfix z rfl
  have hoC : o * z = z * o := Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le _ hoO)
  have hβz : β z = z * o := by rw [ho]; group
  have h2 : (z * o) * (z * o) = 1 := by rw [← hβz, ← map_mul, hz, map_one]
  have h3 : o * o = 1 := by
    calc o * o = (z * z) * (o * o) := by rw [hz, one_mul]
      _ = z * (z * o) * o := by group
      _ = z * (o * z) * o := by rw [hoC]
      _ = (z * o) * (z * o) := by group
      _ = 1 := h2
  rw [hβz, eq_one_of_mem_oddCoreIn_of_mul_self hoO h3, mul_one]

theorem apply_central_eq_of_mod {ζ : Q} (hζ : ζ ∈ Subgroup.center Q)
    (hzζ : (z * ζ) * (z * ζ) = 1) : β ζ = ζ := by
  have hβz := apply_eq_of_mod β hz hfix
  have hζcomm : ∀ g : Q, g * ζ = ζ * g := Subgroup.mem_center_iff.mp hζ
  set o : Q := ζ⁻¹ * β ζ with ho
  have hoO : o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Q)) := hfix ζ (hζcomm z).symm
  have hoc : o ∈ Subgroup.center Q :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hζ) ((apply_mem_center_iff β ζ).mpr hζ)
  have hocomm : ∀ g : Q, g * o = o * g := Subgroup.mem_center_iff.mp hoc
  have hβζ : β ζ = ζ * o := by rw [ho]; group
  have h2 : (z * ζ * o) * (z * ζ * o) = 1 := by
    rw [mul_assoc z ζ o, ← hβζ, ← hβz, ← map_mul, ← map_mul, hzζ, map_one]
  have h3 : o * o = 1 := by
    calc o * o = ((z * ζ) * (z * ζ)) * (o * o) := by rw [hzζ, one_mul]
      _ = (z * ζ) * ((z * ζ) * o) * o := by group
      _ = (z * ζ) * (o * (z * ζ)) * o := by rw [hocomm (z * ζ)]
      _ = (z * ζ * o) * (z * ζ * o) := by group
      _ = 1 := h2
  rw [hβζ, eq_one_of_mem_oddCoreIn_of_mul_self hoO h3, mul_one]

theorem cocycleMod_mul_comm {c : Q}
    (hc : QuotientGroup.mk' (Subgroup.center Q) c * QuotientGroup.mk' (Subgroup.center Q) z =
      QuotientGroup.mk' (Subgroup.center Q) z * QuotientGroup.mk' (Subgroup.center Q) c) :
    cocycle β c * z = z * cocycle β c := by
  have hβz := apply_eq_of_mod β hz hfix
  have hζc := central_of_mk_commute hc
  set ζ : Q := z⁻¹ * (c * z * c⁻¹) with hζdef
  have hζ : c * z * c⁻¹ = z * ζ := by rw [hζdef]; group
  have hzζ : (z * ζ) * (z * ζ) = 1 := by
    rw [← hζ]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz]; group
  have hβζ : β ζ = ζ := apply_central_eq_of_mod β hz hfix hζc hzζ
  have h1 : β c * z * (β c)⁻¹ = c * z * c⁻¹ := by
    calc β c * z * (β c)⁻¹ = β (c * z * c⁻¹) := by rw [map_mul, map_mul, map_inv, hβz]
      _ = β (z * ζ) := by rw [hζ]
      _ = z * ζ := by rw [map_mul, hβz, hβζ]
      _ = c * z * c⁻¹ := hζ.symm
  show c⁻¹ * β c * z = z * (c⁻¹ * β c)
  calc c⁻¹ * β c * z = c⁻¹ * (β c * z * (β c)⁻¹) * β c := by group
    _ = c⁻¹ * (c * z * c⁻¹) * β c := by rw [h1]
    _ = z * (c⁻¹ * β c) := by group

theorem cocycleMod_conj_mem {c : Q}
    (hc : QuotientGroup.mk' (Subgroup.center Q) c * QuotientGroup.mk' (Subgroup.center Q) z =
      QuotientGroup.mk' (Subgroup.center Q) z * QuotientGroup.mk' (Subgroup.center Q) c)
    {i : Q} (hi : i * z = z * i) :
    cocycle β c * i * (cocycle β c)⁻¹ * i⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Q)) := by
  set C : Subgroup Q := Subgroup.centralizer ({z} : Set Q) with hC
  set e : Q := cocycle β c with he
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (cocycleMod_mul_comm β hz hfix hc)
  have hiC : i ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hi
  have hβc : β c = c * e := by rw [he, cocycle]; group
  set o₂ : Q := i⁻¹ * β i with ho₂
  have ho₂O : o₂ ∈ oddCoreIn C := hfix i hi
  have hβi : β i = i * o₂ := by rw [ho₂]; group
  have hj : (c * i * c⁻¹) * z = z * (c * i * c⁻¹) := conj_mul_comm_of_mk hc hi
  set o₁ : Q := (c * i * c⁻¹)⁻¹ * β (c * i * c⁻¹) with ho₁
  have ho₁O : o₁ ∈ oddCoreIn C := hfix _ hj
  have hβj : β (c * i * c⁻¹) = (c * i * c⁻¹) * o₁ := by rw [ho₁]; group
  have h1 : β (c * i * c⁻¹) = (c * e) * (i * o₂) * (c * e)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hβc, hβi]
  have hkey : e * i * o₂ * e⁻¹ = i * (c⁻¹ * o₁ * c) := by
    calc e * i * o₂ * e⁻¹ = c⁻¹ * ((c * e) * (i * o₂) * (c * e)⁻¹) * c := by group
      _ = c⁻¹ * ((c * i * c⁻¹) * o₁) * c := by rw [← h1, hβj]
      _ = i * (c⁻¹ * o₁ * c) := by group
  have hc' : c⁻¹ * o₁ * c ∈ oddCoreIn C := by
    have := apply_mem_oddCoreIn_of_map_eq (MulAut.conj c⁻¹)
      (map_conj_centralizer_of_mk (mk_commute_inv hc)) ho₁O
    simpa [MulAut.conj_apply] using this
  have he' : e * o₂⁻¹ * e⁻¹ ∈ oddCoreIn C := conj_mem_oddCoreIn heC ((oddCoreIn C).inv_mem ho₂O)
  have h2 : e * i * e⁻¹ * i⁻¹ = i * ((c⁻¹ * o₁ * c) * (e * o₂⁻¹ * e⁻¹)) * i⁻¹ := by
    calc e * i * e⁻¹ * i⁻¹ = (e * i * o₂ * e⁻¹) * (e * o₂⁻¹ * e⁻¹) * i⁻¹ := by group
      _ = (i * (c⁻¹ * o₁ * c)) * (e * o₂⁻¹ * e⁻¹) * i⁻¹ := by rw [hkey]
      _ = i * ((c⁻¹ * o₁ * c) * (e * o₂⁻¹ * e⁻¹)) * i⁻¹ := by group
  rw [h2]
  exact conj_mem_oddCoreIn hiC ((oddCoreIn C).mul_mem hc' he')

theorem cocycleMod_pow_mem {m : ℕ} (hβm : β ^ m = 1) {c : Q}
    (hc : QuotientGroup.mk' (Subgroup.center Q) c * QuotientGroup.mk' (Subgroup.center Q) z =
      QuotientGroup.mk' (Subgroup.center Q) z * QuotientGroup.mk' (Subgroup.center Q) c) :
    cocycle β c ^ m ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Q)) := by
  set C : Subgroup Q := Subgroup.centralizer ({z} : Set Q) with hC
  set e : Q := cocycle β c with he
  have hβz := apply_eq_of_mod β hz hfix
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (cocycleMod_mul_comm β hz hfix hc)
  have hβc : β c = c * e := by rw [he, cocycle]; group
  set oe : Q := e⁻¹ * β e with hoe
  have hoeO : oe ∈ oddCoreIn C := hfix e (Subgroup.mem_centralizer_singleton_iff.mp heC)
  have hβe : β e = e * oe := by rw [hoe]; group
  have hβO : ∀ w ∈ oddCoreIn C, β w ∈ oddCoreIn C := fun w hw =>
    apply_mem_oddCoreIn_of_map_eq β (map_centralizer_of_apply_eq β hβz) hw
  have key : ∀ j : ℕ, ∃ w ∈ oddCoreIn C, (β ^ j) c = c * e ^ j * w := by
    intro j
    induction j with
    | zero => exact ⟨1, (oddCoreIn C).one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨w, hw, hwj⟩ := ih
      obtain ⟨w', hw', hw'j⟩ := exists_pow_mul_mem_oddCoreIn heC hoeO j
      refine ⟨w' * β w, (oddCoreIn C).mul_mem hw' (hβO w hw), ?_⟩
      rw [pow_succ', MulAut.mul_apply, hwj, map_mul, map_mul, map_pow, hβc, hβe, hw'j,
        pow_succ']
      group
  obtain ⟨w, hw, hwm⟩ := key m
  rw [hβm, MulAut.one_apply] at hwm
  have h1 : e ^ m = w⁻¹ := by
    have h2 : c * (e ^ m * w) = c * 1 := by rw [← mul_assoc, ← hwm, mul_one]
    have h3 := mul_left_cancel h2
    exact eq_inv_of_mul_eq_one_left h3
  rw [h1]
  exact (oddCoreIn C).inv_mem hw

end Facts

section Main

variable {Q : Type} [Group Q] [Finite Q]

theorem cocycle_mem_oddCoreIn_of_mod (β : MulAut Q) {m : ℕ} (hm : Odd m) (hβm : β ^ m = 1)
    {z : Q} (hz : z * z = 1)
    (hfix : ∀ c : Q, c * z = z * c → c⁻¹ * β c ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Q)))
    (c : Q)
    (hc : QuotientGroup.mk' (Subgroup.center Q) c ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (Subgroup.center Q) z} : Set (Q ⧸ Subgroup.center Q))) :
    (QuotientGroup.mk' (Subgroup.center Q) c)⁻¹ *
        centerQuotAut β (QuotientGroup.mk' (Subgroup.center Q) c) ∈
      oddCoreIn (Subgroup.centralizer
        ({QuotientGroup.mk' (Subgroup.center Q) z} : Set (Q ⧸ Subgroup.center Q))) := by
  classical
  set π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q) with hπ
  set M : Subgroup (Q ⧸ Subgroup.center Q) :=
    Subgroup.centralizer ({π z} : Set (Q ⧸ Subgroup.center Q)) with hM
  set C : Subgroup Q := Subgroup.centralizer ({z} : Set Q) with hC
  have hmk : ∀ d : Q, π d ∈ M → π d * π z = π z * π d := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mp hd
  have hE : ∀ d : Q, π d ∈ M → cocycle β d ∈ C := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr (cocycleMod_mul_comm β hz hfix (hmk d hd))
  set E₀ : Set Q := {x | ∃ d : Q, π d ∈ M ∧ x = cocycle β d} with hE₀
  set B₁ : Subgroup Q := Subgroup.closure (E₀ ∪ (oddCoreIn C : Set Q)) with hB₁
  have hB₁C : B₁ ≤ C := by
    rw [hB₁, Subgroup.closure_le]
    rintro x (⟨d, hd, rfl⟩ | hx)
    · exact hE d hd
    · exact oddCoreIn_le C hx
  have hON : ((oddCoreIn C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreIn_le C)).mpr (normalizer_oddCoreIn C)
  set ρ : C →* C ⧸ (oddCoreIn C).subgroupOf C := QuotientGroup.mk' _ with hρ
  have hρ1 : ∀ x : C, (x : Q) ∈ oddCoreIn C → ρ x = 1 := fun x hx =>
    (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hx)
  set Eρ : Set (C ⧸ (oddCoreIn C).subgroupOf C) :=
    {y | ∃ d : Q, ∃ hd : π d ∈ M, y = ρ ⟨cocycle β d, hE d hd⟩} with hEρ
  set A : Subgroup (C ⧸ (oddCoreIn C).subgroupOf C) := Subgroup.closure Eρ with hA
  have hEcomm : ∀ x ∈ Eρ, ∀ y ∈ Eρ, Commute x y := by
    rintro _ ⟨d₁, hd₁, rfl⟩ _ ⟨d₂, hd₂, rfl⟩
    have h1 := cocycleMod_conj_mem β hz hfix (hmk d₁ hd₁)
      (Subgroup.mem_centralizer_singleton_iff.mp (hE d₂ hd₂))
    set a : C := ⟨cocycle β d₁, hE d₁ hd₁⟩ with ha
    set b : C := ⟨cocycle β d₂, hE d₂ hd₂⟩ with hb
    have h2 : ρ (a * b * a⁻¹ * b⁻¹) = 1 := hρ1 _ h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    have h3 : ρ a * ρ b * (ρ a)⁻¹ = ρ b := mul_inv_eq_one.mp h2
    show ρ a * ρ b = ρ b * ρ a
    calc ρ a * ρ b = ρ a * ρ b * (ρ a)⁻¹ * ρ a := by group
      _ = ρ b * ρ a := by rw [h3]
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, Commute x y := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => Commute x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hx hy
    · intro x y hx hy
      exact hEcomm x hx y hy
    · intro x _
      exact Commute.one_left x
    · intro x _
      exact Commute.one_right x
    · intro x y z _ _ _ hxz hyz
      exact hxz.mul_left hyz
    · intro y z x _ _ _ hxy hxz
      exact hxy.mul_right hxz
    · intro x y _ _ h
      exact h.inv_left
    · intro x y _ _ h
      exact h.inv_right
  have hApow : ∀ x ∈ A, x ^ m = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ^ m = 1) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨d, hd, rfl⟩
      rw [← map_pow]
      apply hρ1
      simpa using cocycleMod_pow_mem β hz hfix hβm (hmk d hd)
    · exact one_pow m
    · intro x y hx hy hxm hym
      rw [(hAcomm x hx y hy).mul_pow, hxm, hym, one_mul]
    · intro x _ hxm
      rw [inv_pow, hxm, inv_one]
  have hB₁ρ : ∀ b ∈ B₁, ∃ hb : b ∈ C, ρ ⟨b, hb⟩ ∈ A := by
    intro b hb
    refine Subgroup.closure_induction (p := fun b _ => ∃ hb : b ∈ C, ρ ⟨b, hb⟩ ∈ A) ?_ ?_ ?_ ?_
      hb
    · rintro x (⟨d, hd, rfl⟩ | hx)
      · exact ⟨hE d hd, Subgroup.subset_closure ⟨d, hd, rfl⟩⟩
      · refine ⟨oddCoreIn_le C hx, ?_⟩
        rw [hρ1 _ hx]
        exact A.one_mem
    · refine ⟨C.one_mem, ?_⟩
      rw [show (⟨1, C.one_mem⟩ : C) = 1 from rfl, map_one]
      exact A.one_mem
    · rintro x y _ _ ⟨hx, hxA⟩ ⟨hy, hyA⟩
      refine ⟨C.mul_mem hx hy, ?_⟩
      rw [show (⟨x * y, C.mul_mem hx hy⟩ : C) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
      exact A.mul_mem hxA hyA
    · rintro x _ ⟨hx, hxA⟩
      refine ⟨C.inv_mem hx, ?_⟩
      rw [show (⟨x⁻¹, C.inv_mem hx⟩ : C) = (⟨x, hx⟩ : C)⁻¹ from rfl, map_inv]
      exact A.inv_mem hxA
  have hB₁odd : ∀ b ∈ B₁, Odd (orderOf b) := by
    intro b hb
    obtain ⟨hbC, hbA⟩ := hB₁ρ b hb
    have h1 : ρ (⟨b, hbC⟩ ^ m) = 1 := by rw [map_pow]; exact hApow _ hbA
    have h2 : b ^ m ∈ oddCoreIn C := by
      have := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
      simpa using this
    have h3 : (b ^ m) ^ Nat.card (oddCoreIn C) = 1 := by
      have := congrArg Subtype.val (pow_card_eq_one' (G := oddCoreIn C) (x := ⟨b ^ m, h2⟩))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h4 : orderOf b ∣ m * Nat.card (oddCoreIn C) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact h3)
    exact (hm.mul (odd_card_oddCoreIn C)).of_dvd_nat h4
  set B : Subgroup (Q ⧸ Subgroup.center Q) := B₁.map π with hB
  have hBM : B ≤ M := by
    rintro _ ⟨b, hb, rfl⟩
    have hbC := Subgroup.mem_centralizer_singleton_iff.mp (hB₁C hb)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hbC]
  have hBodd : Odd (Nat.card B) := by
    refine odd_natCard_of_forall_odd_orderOf B ?_
    rintro _ ⟨b, hb, rfl⟩
    exact (hB₁odd b hb).of_dvd_nat (orderOf_map_dvd π b)
  have hconjB₁ : ∀ d : Q, π d ∈ M → ∀ b ∈ B₁, d * b * d⁻¹ ∈ B₁ := by
    intro d hd b hb
    refine Subgroup.closure_induction (p := fun b _ => d * b * d⁻¹ ∈ B₁) ?_ ?_ ?_ ?_ hb
    · rintro x (⟨c', hc', rfl⟩ | hx)
      · have hd' : π d⁻¹ ∈ M := by rw [map_inv]; exact M.inv_mem hd
        have hcd : π (c' * d⁻¹) ∈ M := by
          rw [map_mul, map_inv]
          exact M.mul_mem hc' (M.inv_mem hd)
        have key : d * cocycle β c' * d⁻¹ = cocycle β (c' * d⁻¹) * (cocycle β d⁻¹)⁻¹ := by
          simp only [cocycle, map_mul, map_inv]
          group
        rw [key]
        exact B₁.mul_mem (Subgroup.subset_closure (Or.inl ⟨_, hcd, rfl⟩))
          (B₁.inv_mem (Subgroup.subset_closure (Or.inl ⟨_, hd', rfl⟩)))
      · have := apply_mem_oddCoreIn_of_map_eq (MulAut.conj d)
          (map_conj_centralizer_of_mk (hmk d hd)) hx
        exact Subgroup.subset_closure (Or.inr (by simpa [MulAut.conj_apply] using this))
    · simp
    · intro x y _ _ hx hy
      have : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
      rw [this]
      exact B₁.mul_mem hx hy
    · intro x _ hx
      have : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
      rw [this]
      exact B₁.inv_mem hx
  have hnorm : M ≤ Subgroup.normalizer (B : Set (Q ⧸ Subgroup.center Q)) := by
    refine le_normalizer_of_forall_conj_mem fun d' hd' x hx => ?_
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) d'
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨d * b * d⁻¹, hconjB₁ d hd' b hb, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hBO : B ≤ oddCoreIn M := le_oddCoreIn_of_normalizes hBM hnorm hBodd
  apply hBO
  have e : (π c)⁻¹ * centerQuotAut β (π c) = π (cocycle β c) := by
    rw [centerQuotAut_mk, ← map_inv, ← map_mul]
    rfl
  rw [e]
  exact ⟨cocycle β c, Subgroup.subset_closure (Or.inl ⟨c, hc, rfl⟩), rfl⟩

end Main

end CFSG.ClassicalInvolution.Q3.GlueLie
