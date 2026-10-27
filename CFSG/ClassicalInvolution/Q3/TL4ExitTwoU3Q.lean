module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoU3D
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoU3A
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3Ck
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallU33
public import CFSG.GH74.KGroups.Generic6
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1
public import Certificates.Certificate55113

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups
  CFSG.GH74.KGroups.U33

theorem U3.exists_quat_member {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}
    (hΔ : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) {K : Subgroup G} (hK : K ∈ Δ) {t : G}
    (hKt : IsUniqueInvolution K t) :
    ∃ (P : Subgroup G) (a b : G), IsSylow2In P K ∧ Nonempty (↥P ≃* QuaternionGroup 2) ∧
      U3.QPair P t a b ∧ ∀ r ∈ P, r ∈ q8List t a b := by
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := K) (IsPGroup.of_bot (p := 2)) bot_le
  obtain ⟨eP⟩ := hΔ.quat K hK P hP
  have e : ↥P ≃* QuaternionGroup 2 := eP
  set w : ↥P := e.symm (QuaternionGroup.a 2) with hw
  have hw2 : (w : G) * w = 1 := by
    rw [← Subgroup.coe_mul, hw, ← map_mul,
      show QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2) by decide,
      map_one, Subgroup.coe_one]
  have hw1 : (w : G) ≠ 1 := fun h0 => by
    have h1 : w = 1 := Subtype.ext h0
    rw [hw, MulEquiv.map_eq_one_iff] at h1
    exact absurd h1 (by decide)
  have hwt : (w : G) = t := (hKt.unique _ (hP.1 w.2) hw2).resolve_left hw1
  obtain ⟨a, b, hp, hq⟩ := U3.quat_shape e (hwt ▸ w.2) hKt.sq hKt.ne_one
  exact ⟨P, a, b, hP, ⟨e⟩, hp, hq⟩

theorem socleTransitive_u33 : SocleTransitive IsU33 := by
  intro G _ _ N _ _ _ hC hL Δ hΔ hN J hJ L₀ hL₀
  classical
  obtain ⟨e⟩ := U33.equiv_of_lieModel hL
  obtain ⟨M, hMP, hMA⟩ := U33.autModel e
  have hPA : M.P ≤ M.A := by
    rw [hMP, hMA, QP_closure, u33_QA_closure]
    exact Subgroup.closure_mono fun x hx => by
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  set ψ := M.actHom N with hψ
  have hψi : Function.Injective ψ := M.actHom_injective N hC
  have hψN : ∀ n (hn : n ∈ N), ψ n = (M.e ⟨n, hn⟩ : Equiv.Perm (Fin 28)) := by
    intro n hn
    show (M.Φ (MulAut.conjNormal n) : Equiv.Perm (Fin 28)) = _
    rw [show (MulAut.conjNormal n : MulAut N) = MulAut.conj ⟨n, hn⟩ from
      MulAut.conjNormal_val (h := ⟨n, hn⟩)]
    exact autModel_Φ_conj_eq M hPA ⟨n, hn⟩
  have hle1 : QP.originalSubgroup ≤ ψ.range := by
    intro m hm
    rw [← hMP] at hm
    refine ⟨((M.e.symm ⟨m, hm⟩ : N) : G), ?_⟩
    rw [hψN _ (M.e.symm ⟨m, hm⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hle2 : ψ.range ≤ QA.originalSubgroup := by
    rintro _ ⟨x, rfl⟩
    rw [← hMA]
    exact M.actHom_mem N x
  have hLN : ∀ y, ψ y ∈ elemsT QP ↔ y ∈ N := by
    intro y
    rw [mem_elemsT QP QP_ok]
    constructor
    · intro hy
      rw [← hMP] at hy
      have h1 : ψ ((M.e.symm ⟨ψ y, hy⟩ : N) : G) = ψ y := by
        rw [hψN _ (M.e.symm ⟨ψ y, hy⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
      rw [← hψi h1]
      exact (M.e.symm ⟨ψ y, hy⟩).2
    · intro hy
      rw [hψN y hy, ← hMP]
      exact (M.e ⟨y, hy⟩).2
  have hLN' : ∀ y, ψ y ∈ QP.originalSubgroup ↔ y ∈ N := fun y =>
    (mem_elemsT QP QP_ok _).symm.trans (hLN y)
  have hL0' : ∀ y, ψ y ∈ QA.originalSubgroup := fun y => hle2 ⟨y, rfl⟩
  have ho : ∀ {K : Subgroup G} {z : G}, IsUniqueInvolution K z → orderOf z = 2 := fun hz =>
    orderOf_eq_prime (by rw [sq]; exact hz.sq) hz.ne_one
  obtain ⟨⟨t, ht⟩, -⟩ := hΔ.hyp.omega1 J hJ
  have htN := hN J hJ t ht
  have hF : U3.ExitFacts QP.originalSubgroup QA.originalSubgroup (ψ t) :=
    Certificates.certificate55113 (ψ t) ((hLN' t).2 htN) (by rw [← map_mul, ht.sq, map_one])
      (fun h0 => ht.ne_one (hψi (by rw [h0, map_one])))
  refine transitive_of_eq_at hΔ.hyp (t := t) (fun K hK z hz => ?_)
    (fun K hK K' hK' hKt hK't => ?_) J hJ L₀ hL₀
  · obtain ⟨n, -, hn⟩ := U3.exists_conj_of_psu (p := 3) (f := 1) (by norm_num) hL
      (hN K hK z hz) htN (ho hz) (ho ht)
    exact ⟨n, hn⟩
  obtain ⟨P, a, b, hP, ⟨eP⟩, hp, hPq⟩ := U3.exists_quat_member hΔ hK hKt
  obtain ⟨P', a', b', hP', ⟨eP'⟩, hp', hP'q⟩ := U3.exists_quat_member hΔ hK' hK't
  by_cases hty : (ψ a ∈ QP.originalSubgroup ∧ ψ b ∈ QP.originalSubgroup) ↔
      (ψ a' ∈ QP.originalSubgroup ∧ ψ b' ∈ QP.originalSubgroup)
  · exact U3.eq_of_same_type hψi hL0' hF hΔ hK hK' hKt (hp.mono hP.1) (hp'.mono hP'.1) hty
  exfalso
  have hP6 : Nat.card QP.originalSubgroup = 6048 := by rw [card_group QP QP_ok, QP_valid.2]
  have hA : Nat.card QA.originalSubgroup = 12096 := by rw [card_group QA QA_ok, QA_valid.2]
  obtain ⟨k, hk⟩ : 6048 ∣ Nat.card ψ.range := hP6 ▸ Subgroup.card_dvd_of_le hle1
  have h2 : Nat.card ψ.range ∣ 12096 := hA ▸ Subgroup.card_dvd_of_le hle2
  have hk2 : k ∣ 2 := by
    rw [hk] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 6048) (by simpa using h2)
  have hR : ψ.range = QA.originalSubgroup := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
    · exfalso
      have hRP : ψ.range = QP.originalSubgroup :=
        (Subgroup.eq_of_le_of_card_ge hle1 (by rw [hk, hP6])).symm
      have hall : ∀ y, ψ y ∈ QP.originalSubgroup := fun y => hRP ▸ ⟨y, rfl⟩
      exact hty (iff_of_true ⟨hall a, hall b⟩ ⟨hall a', hall b'⟩)
    · exact Subgroup.eq_of_le_of_card_ge hle2 (by rw [hk, hA])
  have hLs : ∀ m, m ∈ elemsT QA ↔ ∃ y, ψ y = m := fun m => by
    rw [mem_elemsT QA QA_ok, ← hR]
    rfl
  have hck9 := u33_check_9744
  obtain ⟨r, hr, g, hg⟩ := cover_of_coverB hψi hLs (Bool.and_eq_true_iff.1 hck9).1 (ho ht)
  have hVP := verdictPred_of_check hψi hLs (by norm_num : 100 < 243) hLN hck9 hr
  have hNO : NoOddNormalAt3 t := MF163.U3.noOddNormalAt3_of_conj g (hg ▸ hVP.1)
  have hO : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set G)) = ⊥ :=
    oddCoreImg_eq_bot_3 hNO le_rfl Subgroup.le_normalizer
  have hPK := U3.eq_sylow_of_oddCore hΔ hK hKt hO hP
  have hP'K' := U3.eq_sylow_of_oddCore hΔ hK' hK't hO hP'
  subst hPK hP'K'
  have hLs' : ∀ m, m ∈ QA.originalSubgroup ↔ ∃ y, ψ y = m := fun m => by
    rw [← hR]
    rfl
  by_cases h1 : ψ a ∈ QP.originalSubgroup ∧ ψ b ∈ QP.originalSubgroup <;>
    by_cases h2 : ψ a' ∈ QP.originalSubgroup ∧ ψ b' ∈ QP.originalSubgroup
  · exact hty (iff_of_true h1 h2)
  · exact U3.false_of_mixed hψi hLs' hF hLN' hΔ hK hK' hKt hK't hp hp' hPq eP' h1 h2
  · exact U3.false_of_mixed hψi hLs' hF hLN' hΔ hK' hK hK't hKt hp' hp hP'q eP h2 h1
  · exact hty (iff_of_false h1 h2)

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
