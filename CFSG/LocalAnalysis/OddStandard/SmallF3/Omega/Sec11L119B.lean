module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L119A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma sec11_conj_inv_apply (y v : G) :
    (MulAut.conj y⁻¹).toMonoidHom v = y⁻¹ * v * y := by
  show (MulAut.conj y⁻¹) v = y⁻¹ * v * y
  rw [MulAut.conj_apply, inv_inv]

theorem sec11_Q_le_KD [Finite G] (hp : Asc82Pre11) (h115c : Asc82Lemma115c) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) : secQ K1 K2 ≤ secKD (secD K1 K2 R) := by
  have h10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hsup : secK0 t z = secKD (secD K1 K2 R) ⊔ oddCoreIn (secK0 t z) :=
    (h115c G t L S z K1 K2 T R hctx).2
  have hQeq : secQ K1 K2 = S ⊓ secK0 t z :=
    sec11_Q_eq_inf hp.r10.lK0 hp.s3.l36 hp.facts.pockets5 hp.facts.centZ5 hp.basic h10
  have hQK0 : secQ K1 K2 ≤ secK0 t z := by rw [hQeq]; exact inf_le_right
  have hQleS : secQ K1 K2 ≤ S := (sec11_Q_facts hp h10).2.1
  refine sec11_le_of_sup_odd (A := secKD (secD K1 K2 R)) (N := oddCoreIn (secK0 t z))
    (K := secK0 t z) (Q := secQ K1 K2) ?_ ?_ ?_ ?_ hsup ?_ hQK0 ?_
  · exact (oddCoreIn_normal (secK0 t z)).1
  · exact le_trans le_sup_left (le_of_eq hsup.symm)
  · intro k hk n hn
    exact conj_mem_oddCoreIn (Subgroup.le_normalizer hk) hn
  · exact odd_card_oddCoreIn (secK0 t z)
  · exact hctx.sylow.2.1.to_le hQleS
  · intro v hv hv2
    exact sec10T_two_elem_K0 hp.r10.lK0 hp.s3.l36 hp.facts.pockets5 hp.facts.centZ5
      hp.basic h10 hv hv2

theorem sec11_N_DQ_le_N_Q [Finite G] (hp : Asc82Pre11) (h115c : Asc82Lemma115c)
    (h118 : Asc82Lemma118) {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) {y : G} (hy : y ∈ centralizer ({z} : Set G))
    (hDQ : y ∈ normalizer ((secD K1 K2 R ⊔ secQ K1 K2 : Subgroup G) : Set G)) :
    y ∈ normalizer (secQ K1 K2 : Set G) := by
  set Q : Subgroup G := secQ K1 K2 with hQ
  set D : Subgroup G := secD K1 K2 R with hD
  have h10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have htD : t ∈ D := sec11_t_mem_D hp hctx
  have hzD : z ∈ D := sec11_z_mem_D hp hctx
  have hQKD : Q ≤ secKD D := sec11_Q_le_KD hp h115c hctx
  have hytDQ : y * t * y⁻¹ ∈ D ⊔ Q :=
    (Subgroup.mem_normalizer_iff.mp hDQ t).mp (Subgroup.mem_sup_left htD)
  have hsD : y * t * y⁻¹ ∈ D := by
    have h := h118 G t L S z K1 K2 T R hctx y⁻¹ (Subgroup.inv_mem _ hy) (by simpa using hytDQ)
    simpa using h
  have hcent_le : centralizer (D : Set G) ≤
      centralizer ({y * t * y⁻¹} : Set G) ⊓ centralizer ({z} : Set G) := by
    refine le_inf ?_ ?_
    · exact Subgroup.centralizer_le (fun a ha => by
        rw [Set.mem_singleton_iff] at ha; rw [ha]; exact hsD)
    · exact Subgroup.centralizer_le (fun a ha => by
        rw [Set.mem_singleton_iff] at ha; rw [ha]; exact hzD)
  have hoTwo_le : oTwoRes (centralizer (D : Set G)) ≤
      oTwoRes (centralizer ({y * t * y⁻¹} : Set G) ⊓ centralizer ({z} : Set G)) := by
    rw [oTwoRes, oTwoRes]
    exact Subgroup.closure_mono (fun x hx => ⟨hcent_le hx.1, hx.2⟩)
  have hQoTwo : Q ≤
      oTwoRes (centralizer ({y * t * y⁻¹} : Set G) ⊓ centralizer ({z} : Set G)) :=
    fun v hv => hoTwo_le (hQKD hv)
  have hconjX : ∀ x ∈ centralizer ({y * t * y⁻¹} : Set G) ⊓ centralizer ({z} : Set G),
      y⁻¹ * x * y ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxs : x * (y * t * y⁻¹) = (y * t * y⁻¹) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx1
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx2
    have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hyz_inv : y⁻¹ * z = z * y⁻¹ := by
      calc y⁻¹ * z = y⁻¹ * (z * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * z) * y⁻¹ := by rw [← hyz]
        _ = z * y⁻¹ := by group
    have h1 : (y⁻¹ * x * y) * t = t * (y⁻¹ * x * y) := by
      calc (y⁻¹ * x * y) * t = y⁻¹ * (x * (y * t * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * t * y⁻¹) * x) * y := by rw [hxs]
        _ = t * (y⁻¹ * x * y) := by group
    have h2 : (y⁻¹ * x * y) * z = z * (y⁻¹ * x * y) := by
      calc (y⁻¹ * x * y) * z = y⁻¹ * (x * (y * z)) := by group
        _ = y⁻¹ * (x * (z * y)) := by rw [hyz]
        _ = y⁻¹ * (x * z) * y := by group
        _ = y⁻¹ * (z * x) * y := by rw [hxz]
        _ = (y⁻¹ * z) * (x * y) := by group
        _ = (z * y⁻¹) * (x * y) := by rw [hyz_inv]
        _ = z * (y⁻¹ * x * y) := by group
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr h1,
      Subgroup.mem_centralizer_singleton_iff.mpr h2⟩
  have hmapK0 : ∀ v ∈ Q, y⁻¹ * v * y ∈ secK0 t z :=
    fun v hv => sec11_conj_mem_oTwoRes hconjX (hQoTwo hv)
  have hmapQ : ∀ v ∈ Q, y⁻¹ * v * y ∈ Q := by
    intro v hv
    have hvS : v ∈ S := (sec11_Q_facts hp h10).2.1 hv
    obtain ⟨m, hm⟩ := hctx.sylow.2.1 ⟨v, hvS⟩
    have hvpow : v ^ (2 ^ m) = 1 := by simpa using hm
    have hv2 : ∃ n : ℕ, (y⁻¹ * v * y) ^ (2 ^ n) = 1 := by
      refine ⟨m, ?_⟩
      rw [← sec11_conj_inv_apply y v, ← map_pow, hvpow, map_one]
    exact sec10T_two_elem_K0 hp.r10.lK0 hp.s3.l36 hp.facts.pockets5 hp.facts.centZ5
      hp.basic h10 (hmapK0 v hv) hv2
  have hQmap_le : Q.map (MulAut.conj y⁻¹).toMonoidHom ≤ Q := by
    rintro w hw
    rw [Subgroup.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [sec11_conj_inv_apply y v]
    exact hmapQ v hv
  have hcard : Nat.card (Q.map (MulAut.conj y⁻¹).toMonoidHom) = Nat.card Q :=
    Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
  have hQmap_eq : Q.map (MulAut.conj y⁻¹).toMonoidHom = Q :=
    Subgroup.eq_of_le_of_card_ge hQmap_le (le_of_eq hcard.symm)
  have hconjQ : ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := by
    intro x hx
    have hxmap : x ∈ Q.map (MulAut.conj y⁻¹).toMonoidHom := hQmap_eq.symm ▸ hx
    rw [Subgroup.mem_map] at hxmap
    obtain ⟨v, hv, hvx⟩ := hxmap
    have hthis : y * x * y⁻¹ = v := by
      rw [← hvx, sec11_conj_inv_apply y v]
      group
    rw [hthis]
    exact hv
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hconjQ x, fun hx => by
    have h' := hmapQ (y * x * y⁻¹) hx
    have hthis : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rwa [hthis] at h'⟩

end CFSG.OddStandard.SmallF3.Omega
