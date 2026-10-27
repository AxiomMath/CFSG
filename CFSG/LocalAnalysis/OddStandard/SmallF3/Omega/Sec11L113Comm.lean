module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Seed

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Equiv

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem sec113_phi_add_ones (hm : Sec11Model t L S z K1 K2 T Alt φ) (w : Fin 6 → ZMod 2) :
    φ (w + fun _ => 1) = φ w := by
  rw [hm.perm.mul, (hm.perm.ker _).2 (Or.inr rfl), mul_one]

theorem sec113_cent_AQ (hm : Sec11Model t L S z K1 K2 T Alt φ) {c : G} (hcA : c ∈ secA t S L)
    (hcQ : ∀ q ∈ secQ K1 K2, q * c = c * q) : c = 1 ∨ c = t ∨ c = t * z ∨ c = z := by
  obtain ⟨v, rfl⟩ := hm.perm.surj c hcA
  have hs1 : swap (2 : Fin 6) 3 * swap 4 5 ∈ sec11V4 := by
    unfold sec11V4
    decide
  have hs2 : swap (2 : Fin 6) 4 * swap 3 5 ∈ sec11V4 := by
    unfold sec11V4
    decide
  obtain ⟨q1, hq1, ha1⟩ := hm.Q_act_surj _ hs1
  obtain ⟨q2, hq2, ha2⟩ := hm.Q_act_surj _ hs2
  have e1 : φ (permVec (swap 2 3 * swap 4 5) v) = φ v := by
    rw [← ha1 v]
    calc q1 * φ v * q1⁻¹ = (φ v * q1) * q1⁻¹ := by rw [hcQ q1 hq1]
      _ = φ v := by group
  have e2 : φ (permVec (swap 2 4 * swap 3 5) v) = φ v := by
    rw [← ha2 v]
    calc q2 * φ v * q2⁻¹ = (φ v * q2) * q2⁻¹ := by rw [hcQ q2 hq2]
      _ = φ v := by group
  have hz := sec113_z_eq hm
  rcases sec113_cent_vec v ((hm.perm.eq_iff _ _).1 e1) ((hm.perm.eq_iff _ _).1 e2) with
    (h | h) | (h | h) | (h | h) | (h | h)
  · exact Or.inl (by rw [h]; exact hm.perm.map_zero)
  · exact Or.inl (by rw [h]; exact (hm.perm.ker _).2 (Or.inr rfl))
  · exact Or.inr (Or.inl (by rw [h, ← hm.t_eq]))
  · exact Or.inr (Or.inl (by rw [h, sec113_phi_add_ones hm, ← hm.t_eq]))
  · exact Or.inr (Or.inr (Or.inl (by rw [h, ← hm.tz_eq])))
  · exact Or.inr (Or.inr (Or.inl (by rw [h, sec113_phi_add_ones hm, ← hm.tz_eq])))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, ← hz])))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, sec113_phi_add_ones hm, ← hz])))

theorem sec113_r_rel (hm : Sec11Model t L S z K1 K2 T Alt φ) {r : G}
    (hract : ∀ v, r * φ v * r⁻¹ = φ (permVec (swap 0 1) v)) :
    r * t * r⁻¹ = t * z ∧ r * z * r⁻¹ = z := by
  constructor
  · have h := hract (Pi.single 0 1)
    rw [sec11_permVec_single, Equiv.swap_apply_left, ← hm.t_eq, ← hm.tz_eq] at h
    exact h
  · have h := hract (Pi.single 0 1 + Pi.single 1 1)
    rw [sec11_permVec_add, sec11_permVec_single, sec11_permVec_single, Equiv.swap_apply_left,
      Equiv.swap_apply_right] at h
    have e : φ (Pi.single (1 : Fin 6) 1 + Pi.single (0 : Fin 6) 1) = z := by
      rw [add_comm, ← sec113_z_eq hm]
    rw [e, ← sec113_z_eq hm] at h
    exact h

theorem sec113_inv_r [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ) {r r' : G}
    (hr2 : r * r = 1) (hrT : r ∈ T) (hrQ : ∀ q ∈ secQ K1 K2, q * r = r * q)
    (hract : ∀ v, r * φ v * r⁻¹ = φ (permVec (swap 0 1) v)) (hr'T : r' ∈ T)
    (hr'2 : r' * r' = 1) (hr'Q : ∀ q ∈ secQ K1 K2, q * r' = r' * q)
    (hρr' : hm.perm.rho r' = swap 0 1) : r' = r ∨ r' = r * z := by
  obtain ⟨ht2, hz2, htz, ht1, hz1⟩ := sec11_invols hctx.toSec10Ctx
  have hTM := sec113_T_le_M hctx
  have hrM : r ∈ secM t S L := hTM hrT
  have hr'M : r' ∈ secM t S L := hTM hr'T
  have hρr : hm.perm.rho r = swap 0 1 := hm.perm.rho_eq hrM _ hract
  have hcT : r * r' ∈ T := T.mul_mem hrT hr'T
  have hcM : r * r' ∈ secM t S L := hTM hcT
  have hρc : hm.perm.rho (r * r') = 1 := by
    rw [hm.perm.rho_mul hrM hr'M, hρr, hρr']
    exact Equiv.swap_mul_self (0 : Fin 6) 1
  have hcA : r * r' ∈ secA t S L := by
    refine hm.cenTA _ hcT fun a ha => ?_
    have h := (hm.perm.rho_eq_one_iff hcM).1 hρc a ha
    calc r * r' * a = (r * r' * a * (r * r')⁻¹) * (r * r') := by group
      _ = a * (r * r') := by rw [h]
  have hcQ : ∀ q ∈ secQ K1 K2, q * (r * r') = (r * r') * q := by
    intro q hq
    calc q * (r * r') = (q * r) * r' := by group
      _ = (r * q) * r' := by rw [hrQ q hq]
      _ = r * (q * r') := by group
      _ = r * (r' * q) := by rw [hr'Q q hq]
      _ = (r * r') * q := by group
  have hrc : r' = r * (r * r') :=
    calc r' = (r * r) * r' := by rw [hr2, one_mul]
      _ = r * (r * r') := by group
  obtain ⟨hrt, hrz⟩ := sec113_r_rel hm hract
  have hrt' : r * t = t * z * r :=
    calc r * t = (r * t * r⁻¹) * r := by group
      _ = t * z * r := by rw [hrt]
  have hsqz : (t * z) * z = t :=
    calc (t * z) * z = t * (z * z) := by group
      _ = t := by rw [hz2]; group
  rcases sec113_cent_AQ hm hcA hcQ with hc | hc | hc | hc
  · left
    rw [hrc, hc, mul_one]
  · exfalso
    rw [hc] at hrc
    rw [hrc] at hr'2
    have hsq : (r * t) * (r * t) = z :=
      calc (r * t) * (r * t) = (t * z * r) * (r * t) := by rw [← hrt']
        _ = t * z * (r * r) * t := by group
        _ = t * z * t := by rw [hr2]; group
        _ = z * t * t := by rw [htz]
        _ = z := by rw [mul_assoc, ht2, mul_one]
    exact hz1 (hsq.symm.trans hr'2)
  · exfalso
    rw [hc] at hrc
    rw [hrc] at hr'2
    have hrtz : r * (t * z) = t * r :=
      calc r * (t * z) = (r * t * r⁻¹) * (r * z * r⁻¹) * r := by group
        _ = (t * z) * z * r := by rw [hrt, hrz]
        _ = t * r := by rw [hsqz]
    have hsq : (r * (t * z)) * (r * (t * z)) = z :=
      calc (r * (t * z)) * (r * (t * z)) = (t * r) * (t * r) := by rw [hrtz]
        _ = t * (r * t) * r := by group
        _ = t * (t * z * r) * r := by rw [hrt']
        _ = (t * t) * z * (r * r) := by group
        _ = z := by rw [ht2, hr2]; group
    exact hz1 (hsq.symm.trans hr'2)
  · right
    rw [hrc, hc]

theorem sec113_conj_r [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ) {r : G}
    (hr2 : r * r = 1) (hrT : r ∈ T) (hrQ : ∀ q ∈ secQ K1 K2, q * r = r * q)
    (hract : ∀ v, r * φ v * r⁻¹ = φ (permVec (swap 0 1) v)) {x : G} (hxT : x ∈ T)
    (hx2 : x * x = 1) (hxS : Sec113TypeS (hm.perm.rho x)) :
    x * r * x⁻¹ = r ∨ x * r * x⁻¹ = r * z := by
  have hctx10 := hctx.toSec10Ctx
  have hTM := sec113_T_le_M hctx
  have hxM : x ∈ secM t S L := hTM hxT
  have hrM : r ∈ secM t S L := hTM hrT
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hTst := asc82Step111T_of hp G t L S z K1 K2 T hctx10 hctx.hyp hctx.sylowT hctx.S_le
  have hρr : hm.perm.rho r = swap 0 1 := hm.perm.rho_eq hrM _ hract
  refine sec113_inv_r hp hctx hm hr2 hrT hrQ hract
    (T.mul_mem (T.mul_mem hxT hrT) (T.inv_mem hxT)) ?_ ?_ ?_
  · calc (x * r * x⁻¹) * (x * r * x⁻¹) = x * (r * r) * x⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  · intro q hq
    have hq' : x⁻¹ * q * x ∈ secQ K1 K2 := by
      have h := (Subgroup.mem_normalizer_iff.mp (hTst.2.2.2 hxT) q).mp hq
      rw [hxinv] at h ⊢
      exact h
    have hrq' := hrQ _ hq'
    calc q * (x * r * x⁻¹) = x * ((x⁻¹ * q * x) * r) * x⁻¹ := by group
      _ = x * (r * (x⁻¹ * q * x)) * x⁻¹ := by rw [hrq']
      _ = (x * r * x⁻¹) * q := by group
  · rw [hm.perm.rho_mul ((secM t S L).mul_mem hxM hrM) ((secM t S L).inv_mem hxM),
      hm.perm.rho_mul hxM hrM, sec113_rho_inv hm hxM, hρr]
    obtain ⟨-, -, hcomm⟩ := hxS.fix
    calc hm.perm.rho x * swap 0 1 * (hm.perm.rho x)⁻¹ =
        (swap 0 1 * hm.perm.rho x) * (hm.perm.rho x)⁻¹ := by rw [hcomm]
      _ = swap 0 1 := by group

theorem sec113_comm [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ) {r : G}
    (hr2 : r * r = 1) (hrT : r ∈ T) (hrQ : ∀ q ∈ secQ K1 K2, q * r = r * q)
    (hract : ∀ v, r * φ v * r⁻¹ = φ (permVec (swap 0 1) v)) {x : G} (hxT : x ∈ T)
    (hx2 : x * x = 1) (hxS : Sec113TypeS (hm.perm.rho x))
    (h1 : ∀ a ∈ twoCoreIn K1, x * a * x⁻¹ ∈ twoCoreIn K1)
    (h2 : ∀ a ∈ twoCoreIn K2, x * a * x⁻¹ ∈ twoCoreIn K2) :
    ∃ x' : G, x' ∈ T ∧ x' * x' = 1 ∧ hm.perm.rho x' = hm.perm.rho x ∧
      (∀ a ∈ twoCoreIn K1, x' * a * x'⁻¹ ∈ twoCoreIn K1) ∧
      (∀ a ∈ twoCoreIn K2, x' * a * x'⁻¹ ∈ twoCoreIn K2) ∧ x' * t = t * x' ∧
      x' * r = r * x' := by
  have hctx10 := hctx.toSec10Ctx
  obtain ⟨ht2, hz2, htz, ht1, hz1⟩ := sec11_invols hctx10
  have hTM := sec113_T_le_M hctx
  have hxM : x ∈ secM t S L := hTM hxT
  have htA : t ∈ secA t S L := by
    have h := hm.perm.mem (Pi.single 0 1)
    rwa [← hm.t_eq] at h
  have htT : t ∈ T := sec113_A_le_T hp hctx htA
  have hxt : x * t = t * x := by
    have h := hm.perm.conj_single hxM 0
    rw [hxS.fix.1, ← hm.t_eq] at h
    calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [h]
  rcases sec113_conj_r hp hctx hm hr2 hrT hrQ hract hxT hx2 hxS with hr | hr
  · refine ⟨x, hxT, hx2, rfl, h1, h2, hxt, ?_⟩
    calc x * r = (x * r * x⁻¹) * x := by group
      _ = r * x := by rw [hr]
  · obtain ⟨hrt, hrz⟩ := sec113_r_rel hm hract
    have htQ : ∀ u ∈ secQ K1 K2, t * u * t⁻¹ = u := fun u hu => by
      have h := (sec11_Q_facts hp hctx10).2.2.2.2 u hu
      calc t * u * t⁻¹ = (u * t) * t⁻¹ := by rw [h]
        _ = u := by group
    have hQ := sec113_Q_eq hp hctx10
    have hQ1 : ∀ u ∈ twoCoreIn K1, u ∈ secQ K1 K2 := fun u hu => by
      rw [hQ]
      exact Subgroup.mem_sup_left hu
    have hQ2 : ∀ u ∈ twoCoreIn K2, u ∈ secQ K1 K2 := fun u hu => by
      rw [hQ]
      exact Subgroup.mem_sup_right hu
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hrt' : r * t = t * z * r :=
      calc r * t = (r * t * r⁻¹) * r := by group
        _ = t * z * r := by rw [hrt]
    have hzr : r * z = z * r :=
      calc r * z = (r * z * r⁻¹) * r := by group
        _ = z * r := by rw [hrz]
    have htrt : t * r * t = z * r :=
      calc t * r * t = t * (r * t) := by group
        _ = t * (t * z * r) := by rw [hrt']
        _ = (t * t) * z * r := by group
        _ = z * r := by rw [ht2]; group
    have htzt : t * z * t = z :=
      calc t * z * t = z * t * t := by rw [htz]
        _ = z := by rw [mul_assoc, ht2, mul_one]
    have hconj : t * (r * z) * t⁻¹ = r :=
      calc t * (r * z) * t⁻¹ = t * (r * z) * t := by rw [htinv]
        _ = t * r * (t * t) * z * t := by rw [ht2]; group
        _ = (t * r * t) * (t * z * t) := by group
        _ = (z * r) * z := by rw [htrt, htzt]
        _ = z * (r * z) := by group
        _ = z * (z * r) := by rw [hzr]
        _ = (z * z) * r := by group
        _ = r := by rw [hz2]; group
    refine ⟨t * x, T.mul_mem htT hxT, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc t * x * (t * x) = t * (x * t) * x := by group
        _ = t * (t * x) * x := by rw [hxt]
        _ = (t * t) * (x * x) := by group
        _ = 1 := by rw [ht2, hx2]; group
    · rw [hm.perm.rho_mul (hTM htT) hxM, sec113_rho_of_mem_A hm htA, one_mul]
    · intro a ha
      have e : t * x * a * (t * x)⁻¹ = t * (x * a * x⁻¹) * t⁻¹ := by group
      rw [e, htQ _ (hQ1 _ (h1 a ha))]
      exact h1 a ha
    · intro a ha
      have e : t * x * a * (t * x)⁻¹ = t * (x * a * x⁻¹) * t⁻¹ := by group
      rw [e, htQ _ (hQ2 _ (h2 a ha))]
      exact h2 a ha
    · calc t * x * t = t * (x * t) := by group
        _ = t * (t * x) := by rw [hxt]
    · calc (t * x) * r = ((t * x) * r * (t * x)⁻¹) * (t * x) := by group
        _ = (t * (x * r * x⁻¹) * t⁻¹) * (t * x) := by group
        _ = (t * (r * z) * t⁻¹) * (t * x) := by rw [hr]
        _ = r * (t * x) := by rw [hconj]

end CFSG.OddStandard.SmallF3.Omega
