module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R1a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH1

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}

private theorem s888r1b_card_sup_mul_card_inf_of_commute {H : Type*} [Group H]
    (L R : Subgroup H) (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) =
      Nat.card L * Nat.card R := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]; exact this

private theorem s888r1b_pair_eq_sup (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) :
    Sec5B517Q8.pair hq i j = (Sec5B517Q8 hq ⊓ K i) ⊔ (Sec5B517Q8 hq ⊓ K j) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, ha4, hb4, rfl⟩ := (Sec5B517Q8.mem_pair_iff hq hij).mp hx
    exact Subgroup.mul_mem_sup ⟨Sec5B517Q8.mem_of_mem hq ha ha4, ha⟩
      ⟨Sec5B517Q8.mem_of_mem hq hb hb4, hb⟩
  · refine sup_le ?_ ?_
    · intro x hx
      exact (Sec5B517Q8.mem_pair_iff hq hij).mpr
        ⟨x, hx.2, 1, (K j).one_mem, Sec5B517Q8.pow_four hq hx.1, by simp,
          by rw [mul_one]⟩
    · intro x hx
      exact (Sec5B517Q8.mem_pair_iff hq hij).mpr
        ⟨1, (K i).one_mem, x, hx.2, by simp, Sec5B517Q8.pow_four hq hx.1,
          by rw [one_mul]⟩

private theorem s888r1b_inf_eq_zpowers (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) :
    (Sec5B517Q8 hq ⊓ K i) ⊓ (Sec5B517Q8 hq ⊓ K j) = zpowers z := by
  apply le_antisymm
  · intro x hx
    have hxKi : x ∈ K i := hx.1.2
    have hxKj : x ∈ K j := hx.2.2
    have hcomm : ∀ v ∈ K i, x * v = v * x :=
      fun v hv => hq.comm j i hij.symm x hxKj v hv
    rcases hq.eq_of_central hxKi hcomm with h1 | hz
    · rw [h1]; exact (zpowers z).one_mem
    · rw [hz]; exact Subgroup.mem_zpowers z
  · refine le_inf ?_ ?_
    · exact Subgroup.zpowers_le.mpr (z_mem_inf_K hq i)
    · exact Subgroup.zpowers_le.mpr (z_mem_inf_K hq j)

private theorem s888r1b_card_zpowers (hq : Sec5B517Quad K z) : Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hq.z_sq) hq.z_ne

theorem Sec5B517Q8.card_pair (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) :
    Nat.card ↥(Sec5B517Q8.pair hq i j) = 32 := by
  have hc : ∀ a ∈ (Sec5B517Q8 hq ⊓ K i), ∀ b ∈ (Sec5B517Q8 hq ⊓ K j),
      a * b = b * a :=
    fun a ha b hb => hq.comm i j hij a ha.2 b hb.2
  have hprod := s888r1b_card_sup_mul_card_inf_of_commute
    (Sec5B517Q8 hq ⊓ K i) (Sec5B517Q8 hq ⊓ K j) hc
  rw [s888r1b_inf_eq_zpowers hq hij, s888r1b_card_zpowers hq,
    card_inf_K hq i, card_inf_K hq j] at hprod
  have hsup : Nat.card ↥(Sec5B517Q8.pair hq i j) =
      Nat.card ((Sec5B517Q8 hq ⊓ K i) ⊔ (Sec5B517Q8 hq ⊓ K j) : Subgroup G) := by
    rw [s888r1b_pair_eq_sup hq hij]
  rw [hsup]
  omega

theorem Sec5B517Q8.central_pair (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {x : G}
    (hx : x ∈ Sec5B517Q8.pair hq i j)
    (h : ∀ y ∈ Sec5B517Q8.pair hq i j, x * y = y * x) : x ∈ zpowers z := by
  obtain ⟨a, ha, b, hb, ha4, hb4, hx_eq⟩ := (Sec5B517Q8.mem_pair_iff hq hij).mp hx
  have ha_cent : a = 1 ∨ a = z := by
    refine hq.eq_of_central_q8 ha ha4 ?_
    intro v hv hv4
    have hvpair : v ∈ Sec5B517Q8.pair hq i j :=
      (Sec5B517Q8.mem_pair_iff hq hij).mpr
        ⟨v, hv, 1, (K j).one_mem, hv4, by simp, by rw [mul_one]⟩
    have hh := h v hvpair
    rw [hx_eq] at hh
    have hbv : b * v = v * b := hq.comm j i hij.symm b hb v hv
    exact mul_right_cancel (b := b) (by
      calc a * v * b = a * (v * b) := by group
        _ = a * (b * v) := by rw [hbv]
        _ = (a * b) * v := by group
        _ = v * (a * b) := hh
        _ = v * a * b := by group)
  have hb_cent : b = 1 ∨ b = z := by
    refine hq.eq_of_central_q8 hb hb4 ?_
    intro v hv hv4
    have hvpair : v ∈ Sec5B517Q8.pair hq i j :=
      (Sec5B517Q8.mem_pair_iff hq hij).mpr
        ⟨1, (K i).one_mem, v, hv, by simp, hv4, by rw [one_mul]⟩
    have hh := h v hvpair
    rw [hx_eq] at hh
    have hav : a * v = v * a := hq.comm i j hij a ha v hv
    exact mul_left_cancel (a := a) (by
      calc a * (b * v) = (a * b) * v := by group
        _ = v * (a * b) := hh
        _ = v * a * b := by group
        _ = a * v * b := by rw [hav]
        _ = a * (v * b) := by group)
  rcases ha_cent with h1 | hz
  · rcases hb_cent with h1' | hz'
    · rw [hx_eq, h1, h1', one_mul]; exact (zpowers z).one_mem
    · rw [hx_eq, h1, hz', one_mul]; exact Subgroup.mem_zpowers z
  · rcases hb_cent with h1' | hz'
    · rw [hx_eq, hz, h1', mul_one]; exact Subgroup.mem_zpowers z
    · rw [hx_eq, hz, hz', hq.z_sq]; exact (zpowers z).one_mem

theorem Sec5B517Q8.exists_pair_mul (hq : Sec5B517Quad K z) {x : G} (hx : x ∈ Sec5B517Q8 hq) :
    ∃ a ∈ Sec5B517Q8.pair hq 0 1, ∃ b ∈ Sec5B517Q8.pair hq 2 3, x = a * b := by
  obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hx
  refine ⟨k 0 * k 1, ?_, k 2 * k 3, ?_, ?_⟩
  · exact (Sec5B517Q8.mem_pair_iff hq (show (0 : Fin 4) ≠ 1 by decide)).mpr
      ⟨k 0, (hk 0).1, k 1, (hk 1).1, (hk 0).2, (hk 1).2, rfl⟩
  · exact (Sec5B517Q8.mem_pair_iff hq (show (2 : Fin 4) ≠ 3 by decide)).mpr
      ⟨k 2, (hk 2).1, k 3, (hk 3).1, (hk 2).2, (hk 3).2, rfl⟩
  · simp only [Sec5B517Prod]
    group

end CFSG.OddStandard.SmallF3.Omega
