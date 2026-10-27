module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenFpf
public import CFSG.LocalAnalysis.OddStandard.AltStdSecHerCop

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section CentO

variable {N : Type*} [Group N]

theorem normal_of_le_center' {R : Subgroup N} (hRc : R ≤ Subgroup.center N) : R.Normal :=
  ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hRc hn) g
    rw [this]; simpa using hn⟩

theorem perfect_centralizes_oddCore [Finite N] {O R Q : Subgroup N} [O.Normal]
    (hOodd : ∀ x ∈ O, Odd (orderOf x)) (hRO : R ≤ O) (hRc : R ≤ Subgroup.center N) {z : N}
    (hz : z * z = 1) (hCz : ∀ u ∈ O, z * u * z⁻¹ = u → u ∈ R) (hQ : ⁅Q, Q⁆ = Q)
    (hQz : ∀ a ∈ Q, ∀ b ∈ Q, a * (z * b * z⁻¹) * a⁻¹ * (z * b * z⁻¹)⁻¹ ∈ O) :
    ∀ q ∈ Q, ∀ u ∈ O, q * u = u * q := by
  have : R.Normal := normal_of_le_center' hRc
  have stage1 : ∀ q ∈ Q, ∀ u ∈ O, q * u * q⁻¹ * u⁻¹ ∈ R := by
    let πR : N →* N ⧸ R := QuotientGroup.mk' R
    have hsurj : Function.Surjective πR := QuotientGroup.mk'_surjective R
    set V : Subgroup (N ⧸ R) := O.map πR with hV
    have : V.Normal := Subgroup.Normal.map ‹O.Normal› πR hsurj
    set t : N ⧸ R := πR z with htdef
    have ht : t * t = 1 := by rw [htdef, ← map_mul, hz, map_one]
    have hfpf : ∀ v ∈ V, t * v * t⁻¹ = v → v = 1 := by
      intro v hv htv
      obtain ⟨u, hu, rfl⟩ := hv
      have h1 : z * u * z⁻¹ * u⁻¹ ∈ R := by
        rw [← QuotientGroup.eq_one_iff]
        have : πR (z * u * z⁻¹ * u⁻¹) = t * πR u * t⁻¹ * (πR u)⁻¹ := by
          simp [htdef, map_mul, map_inv]
        rw [show ((z * u * z⁻¹ * u⁻¹ : N) : N ⧸ R) = πR (z * u * z⁻¹ * u⁻¹) from rfl, this, htv]
        group
      have h2 : u * z * u⁻¹ * z⁻¹ ∈ R := by
        have : u * z * u⁻¹ * z⁻¹ = (z * u * z⁻¹ * u⁻¹)⁻¹ := by group
        rw [this]; exact R.inv_mem h1
      obtain ⟨p, hp, hpu⟩ := exists_mul_mem_centralizer (P := R)
        (fun x hx => hOodd x (hRO hx)) hz h2
      have hpuz : z * (p * u) * z⁻¹ = p * u := by
        have := Subgroup.mem_centralizer_singleton_iff.1 hpu
        rw [← this]; group
      have h3 : p * u ∈ R := hCz _ (O.mul_mem (hRO hp) hu) hpuz
      have h4 : u ∈ R := by simpa using R.mul_mem (R.inv_mem hp) h3
      exact (QuotientGroup.eq_one_iff u).2 h4
    obtain ⟨hinv, hcomm⟩ := fpf_inverts_abelian (V := V) ht hfpf
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hQbar : ⁅Q.map πR, Q.map πR⁆ = Q.map πR := by rw [← Subgroup.map_commutator, hQ]
    have hVV : ∀ c ∈ V, ∀ w ∈ V, c * w * c⁻¹ = w := by
      intro c hc w hw
      rw [hcomm c hc w hw]; group
    have hconj : ∀ (x v : N ⧸ R), v ∈ V →
        (t * x * t⁻¹) * v * (t * x * t⁻¹)⁻¹ = x * v * x⁻¹ := by
      intro x v hv
      have h1 : t⁻¹ * v * t = v⁻¹ := by
        have := hinv v hv
        rw [hti] at this ⊢
        exact this
      have hxv : x * v * x⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem v hv x
      calc (t * x * t⁻¹) * v * (t * x * t⁻¹)⁻¹ = t * (x * (t⁻¹ * v * t) * x⁻¹) * t⁻¹ := by group
        _ = t * (x * v⁻¹ * x⁻¹) * t⁻¹ := by rw [h1]
        _ = t * (x * v * x⁻¹)⁻¹ * t⁻¹ := by group
        _ = ((x * v * x⁻¹)⁻¹)⁻¹ := hinv _ (V.inv_mem hxv)
        _ = x * v * x⁻¹ := inv_inv _
    have hmain : ∀ a ∈ Q.map πR, ∀ b ∈ Q.map πR,
        a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set (N ⧸ R)) := by
      intro a ha b hb
      obtain ⟨a₀, ha₀, rfl⟩ := ha
      obtain ⟨b₀, hb₀, rfl⟩ := hb
      have hbt : t * πR b₀ * t⁻¹ = πR (z * b₀ * z⁻¹) := by
        simp [htdef, map_mul, map_inv]
      have hcV : πR a₀ * (t * πR b₀ * t⁻¹) * (πR a₀)⁻¹ * (t * πR b₀ * t⁻¹)⁻¹ ∈ V := by
        rw [hbt]
        exact ⟨_, hQz a₀ ha₀ b₀ hb₀, by simp [map_mul, map_inv]⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      set a := πR a₀ with hadef
      set b := πR b₀ with hbdef
      set bt := t * b * t⁻¹ with hbtdef
      have hXY : ∀ w ∈ V, (a * b) * w * (a * b)⁻¹ = (b * a) * w * (b * a)⁻¹ := by
        intro w hw
        have hbw : b * w * b⁻¹ = bt * w * bt⁻¹ := (hconj b w hw).symm
        have haw : a * w * a⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem w hw a
        have hbaw : bt * (a * w * a⁻¹) * bt⁻¹ = b * (a * w * a⁻¹) * b⁻¹ := hconj b _ haw
        have hbaV : (bt * a) * w * (bt * a)⁻¹ ∈ V := by
          have := (inferInstance : V.Normal).conj_mem w hw (bt * a)
          exact this
        calc (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
          _ = a * (bt * w * bt⁻¹) * a⁻¹ := by rw [hbw]
          _ = ((a * bt * a⁻¹ * bt⁻¹) * (bt * a)) * w *
                ((a * bt * a⁻¹ * bt⁻¹) * (bt * a))⁻¹ := by group
          _ = (a * bt * a⁻¹ * bt⁻¹) * ((bt * a) * w * (bt * a)⁻¹) * (a * bt * a⁻¹ * bt⁻¹)⁻¹ := by
                group
          _ = (bt * a) * w * (bt * a)⁻¹ := hVV _ hcV _ hbaV
          _ = bt * (a * w * a⁻¹) * bt⁻¹ := by group
          _ = b * (a * w * a⁻¹) * b⁻¹ := hbaw
          _ = (b * a) * w * (b * a)⁻¹ := by group
      have hw' : (b * a)⁻¹ * v * (b * a) ∈ V := by
        have := (inferInstance : V.Normal).conj_mem v hv (b * a)⁻¹
        simpa using this
      have hk : (a * b * a⁻¹ * b⁻¹) * v * (a * b * a⁻¹ * b⁻¹)⁻¹ = v := by
        calc (a * b * a⁻¹ * b⁻¹) * v * (a * b * a⁻¹ * b⁻¹)⁻¹
            = (a * b) * ((b * a)⁻¹ * v * (b * a)) * (a * b)⁻¹ := by group
          _ = (b * a) * ((b * a)⁻¹ * v * (b * a)) * (b * a)⁻¹ := hXY _ hw'
          _ = v := by group
      calc v * (a * b * a⁻¹ * b⁻¹) = ((a * b * a⁻¹ * b⁻¹) * v * (a * b * a⁻¹ * b⁻¹)⁻¹) *
            (a * b * a⁻¹ * b⁻¹) := by rw [hk]
        _ = (a * b * a⁻¹ * b⁻¹) * v := by group
    have hQle : Q.map πR ≤ Subgroup.centralizer (V : Set (N ⧸ R)) :=
      le_of_comm_mem hQbar hmain
    intro q hq u hu
    have h1 : πR q ∈ Subgroup.centralizer (V : Set (N ⧸ R)) := hQle ⟨q, hq, rfl⟩
    have h2 := Subgroup.mem_centralizer_iff.1 h1 (πR u) ⟨u, hu, rfl⟩
    rw [← QuotientGroup.eq_one_iff]
    show πR (q * u * q⁻¹ * u⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
    group
  intro q hq u hu
  exact centralizes_of_perfect (Q := Q) (D := R) hQ (g := u) (fun a ha => stage1 a ha u hu)
    (fun d hd a _ => (Subgroup.mem_center_iff.1 (hRc hd) a).symm)
    (fun d hd e _ => (Subgroup.mem_center_iff.1 (hRc hd) e).symm) q hq

@[expose] def zConjSub (z : N) (Q : Subgroup N) : Subgroup N := Q.map (MulAut.conj z).toMonoidHom

theorem mem_zConjSub {z : N} {Q : Subgroup N} {x : N} :
    x ∈ zConjSub z Q ↔ ∃ q ∈ Q, z * q * z⁻¹ = x := by
  simp [zConjSub]

theorem zConjSub_centralizes {O Q : Subgroup N} [O.Normal] {z : N}
    (hQO : ∀ q ∈ Q, ∀ u ∈ O, q * u = u * q) :
    ∀ x ∈ zConjSub z Q, ∀ u ∈ O, x * u = u * x := by
  intro x hx u hu
  obtain ⟨q, hq, rfl⟩ := mem_zConjSub.1 hx
  have hu' : z⁻¹ * u * z ∈ O := by
    have := (inferInstance : O.Normal).conj_mem u hu z⁻¹
    simpa using this
  have h := hQO q hq _ hu'
  calc z * q * z⁻¹ * u = z * (q * (z⁻¹ * u * z)) * z⁻¹ := by group
    _ = z * ((z⁻¹ * u * z) * q) * z⁻¹ := by rw [h]
    _ = u * (z * q * z⁻¹) := by group

theorem perfect_commute_zConjSub {O Q : Subgroup N} [O.Normal] {z : N} (hQ : ⁅Q, Q⁆ = Q)
    (hQO : ∀ q ∈ Q, ∀ u ∈ O, q * u = u * q)
    (hQz : ∀ a ∈ Q, ∀ b ∈ Q, a * (z * b * z⁻¹) * a⁻¹ * (z * b * z⁻¹)⁻¹ ∈ O) :
    ∀ a ∈ Q, ∀ x ∈ zConjSub z Q, a * x = x * a := by
  have hQzO := zConjSub_centralizes (z := z) hQO
  have hOsup : ∀ u ∈ O, ∀ e ∈ Q ⊔ zConjSub z Q, e * u = u * e := by
    intro u hu e he
    have hle : Q ⊔ zConjSub z Q ≤ Subgroup.centralizer ({u} : Set N) :=
      sup_le (fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hQO q hq u hu))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hQzO x hx u hu))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
  intro a ha x hx
  obtain ⟨b, hb, rfl⟩ := mem_zConjSub.1 hx
  refine centralizes_of_perfect (Q := Q) (D := (Q ⊔ zConjSub z Q) ⊓ O) hQ (g := z * b * z⁻¹)
    (fun a' ha' => ?_) (fun d hd a' ha' => ?_) (fun d hd e he => ?_) a ha
  · refine Subgroup.mem_inf.2 ⟨?_, hQz a' ha' b hb⟩
    have h1 : a' ∈ Q ⊔ zConjSub z Q := Subgroup.mem_sup_left ha'
    have h2 : z * b * z⁻¹ ∈ Q ⊔ zConjSub z Q := Subgroup.mem_sup_right (mem_zConjSub.2 ⟨b, hb, rfl⟩)
    exact mul_mem (mul_mem (mul_mem h1 h2) (inv_mem h1)) (inv_mem h2)
  · exact (hQO a' ha' d (Subgroup.mem_inf.1 hd).2).symm
  · exact (hOsup d (Subgroup.mem_inf.1 hd).2 e (Subgroup.mem_inf.1 he).1).symm

end CentO

end CFSG.OddStandard.AltStdSec
