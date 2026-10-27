module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoL2A
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1C
public import CFSG.ClassicalInvolution.Q3.TL4MF163Psl
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint CFSG.GorensteinWalter

theorem socleTransitive_l2Sq : SocleTransitive IsL2Sq := by
  intro G _ _ N _ _ hnab hC hP Δ h hmem
  obtain ⟨p, f, hp, hp2, hfe, hl⟩ := hP
  obtain ⟨-, h4, F, _, _, hFcard, ⟨e⟩⟩ := MF163.psl2_of_lieModel hl
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at h4
    · exact h
  have hKF : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf1, hFcard⟩
  have hcard : 3 < Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hFcard])
    intro h0
    have h1 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff F p 2] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)
  have hsq : IsSquare (2 : F) := L2.isSquare_two hp hp2 hfe hFcard
  let θ : PGammaL2 F ≃* MulAut (PSL2 F) := MulEquiv.ofBijective
    (pGammaL2ToMulAutPSL2 F hKF hcard) ⟨pGammaL2ToMulAutPSL2_injective F hKF hcard,
      pGammaL2ToMulAutPSL2_surjective F hFcard hKF hcard⟩
  let Φ : G →* MulAut (PSL2 F) := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N))
  have hΦ : ∀ (x : G) (n : N), Φ x (e n) = e (MulAut.conjNormal x n) := by
    intro x n
    simp [Φ, MulAut.congr_apply]
  have hΦi : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := hΦ x ⟨n, hn⟩
    rw [hx, MulAut.one_apply] at h1
    have h3 := congrArg Subtype.val (e.injective h1)
    rw [MulAut.conjNormal_apply] at h3
    calc n * x = (x * n * x⁻¹) * x := by rw [← h3]
      _ = x * n := by group
  have hΦN : ∀ n : N, Φ n = MulAut.conj (e n) := by
    intro n
    ext w
    obtain ⟨m, rfl⟩ := e.surjective w
    rw [hΦ, MulAut.conj_apply]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  have hinN : ∀ x : G, orderOf x = 4 → (θ.symm (Φ x)).right = 1 → x ∈ N := by
    intro x hx4 hr
    have hbe := MF163.eq_inl_of_right_eq_one hr
    set c : PGL2 F := (θ.symm (Φ x)).left with hcdef
    have hinj : Function.Injective (θ.symm.toMonoidHom.comp Φ) :=
      θ.symm.injective.comp hΦi
    have hco : orderOf c = 4 := by
      have h1 : orderOf (θ.symm (Φ x)) = 4 := by
        have h0 : orderOf (θ.symm (Φ x)) = orderOf x := orderOf_injective _ hinj x
        rw [h0, hx4]
      rw [hbe] at h1
      rwa [orderOf_injective _ SemidirectProduct.inl_injective] at h1
    have hc4 : c ^ 4 = 1 := by rw [← hco]; exact pow_orderOf_eq_one c
    have hc2 : c ^ 2 ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hco] at this
      norm_num at this
    obtain ⟨s, hs⟩ := L2.exists_toPGL_eq hsq hc2 hc4
    have hθ : θ (SemidirectProduct.inl c) = MulAut.conj s := by
      ext w
      apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      show Matrix.ProjectiveSpecialLinearGroup.toPGL
          (pGammaL2ToMulAutPSL2 F hKF hcard (SemidirectProduct.inl c) w) = _
      rw [pGammaL2ToMulAutPSL2_inl, toPGL_pgl2InnerAutPSL2_apply, ← hs, MulAut.conj_apply,
        map_mul, map_mul, map_inv]
    have hxs : Φ x = Φ (e.symm s : N) := by
      rw [hΦN, MulEquiv.apply_symm_apply, ← hθ, ← hbe, MulEquiv.apply_symm_apply]
    rw [hΦi hxs]
    exact (e.symm s).2
  have hmemN : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z →
      ∃ q ∈ K, q ∈ N ∧ orderOf q = 4 ∧ q * q = z := by
    intro K hK z hz
    obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := K) IsPGroup.of_bot bot_le
    obtain ⟨eP⟩ := h.quat K hK P hP
    let ι : QuaternionGroup 2 →* G := P.subtype.comp eP.symm.toMonoidHom
    have hι : Function.Injective ι := fun a b hab => eP.symm.injective (Subtype.ext hab)
    let ρ : QuaternionGroup 2 →* PGammaL2 F := θ.symm.toMonoidHom.comp (Φ.comp ι)
    obtain ⟨g, hg2, hgr⟩ := L2.exists_right_eq_one hKF ρ
    have hgo : orderOf g = 4 := by
      have h1 : ¬ g ^ 2 ^ 1 = 1 := by rw [pow_one, hg2]; decide
      have h3 : g ^ 2 ^ (1 + 1) = 1 := by
        rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hg2]
        decide
      exact orderOf_eq_prime_pow h1 h3
    have hιo : orderOf (ι g) = 4 := by rw [orderOf_injective ι hι, hgo]
    have hiz : ι (QuaternionGroup.a 2) = z := by
      have hm : ι (QuaternionGroup.a 2) ∈ K := hP.1 (eP.symm _).2
      have hsq2 : ι (QuaternionGroup.a 2) * ι (QuaternionGroup.a 2) = 1 := by
        rw [← map_mul, show (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1
          by decide, map_one]
      have hne : ι (QuaternionGroup.a 2) ≠ 1 := fun h1 =>
        absurd (hι (h1.trans (map_one ι).symm)) (by decide)
      exact (hz.unique _ hm hsq2).resolve_left hne
    refine ⟨ι g, hP.1 (eP.symm g).2, hinN _ hιo hgr, hιo, ?_⟩
    rw [← map_mul, ← sq, hg2, hiz]
  let φ : ↥N →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom
  have hφ : Function.Injective φ :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective
  have hU : ∀ z : G, ∀ K ∈ Δ, ∀ K' ∈ Δ, IsUniqueInvolution K z → IsUniqueInvolution K' z →
      K = K' := by
    intro z K hK K' hK' hz hz'
    obtain ⟨q, hqK, hqN, hq4, hqz⟩ := hmemN K hK z hz
    obtain ⟨q', hqK', hqN', -, hqz'⟩ := hmemN K' hK' z hz'
    set a : ↥N := ⟨q, hqN⟩ with ha
    set b : ↥N := ⟨q', hqN'⟩ with hb
    have hao : orderOf (φ a) = 4 := by
      rw [orderOf_injective φ hφ, ← Subgroup.orderOf_coe, ha, hq4]
    have hc4 : φ a ^ 4 = 1 := by rw [← hao]; exact pow_orderOf_eq_one _
    have hc2 : φ a ^ 2 ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hao] at this
      norm_num at this
    have hab : b ^ 2 = a ^ 2 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow, sq, sq]
      exact hqz'.trans hqz.symm
    have hcc : φ b ^ 2 = φ a ^ 2 := by rw [← map_pow, ← map_pow, hab]
    have hqK'' : q ∈ K' := by
      rcases L2.pgl2_eq_or_eq_inv_of_sq_eq h2 hc2 hc4 hcc with h1 | h1
      · have h3 : b = a := hφ h1
        have h4 : q' = q := congrArg Subtype.val h3
        rw [← h4]
        exact hqK'
      · have h3 : b = a⁻¹ := hφ (by rw [h1, map_inv])
        have h4 : q' = q⁻¹ := congrArg Subtype.val h3
        rw [← inv_inv q, ← h4]
        exact K'.inv_mem hqK'
    exact eq_of_orderOf_eq_four h.hyp hK hK' hqK hqK'' hq4
  intro J hJ L hL
  obtain ⟨⟨t, ht⟩, -⟩ := h.hyp.omega1 J hJ
  refine transitive_of_eq_at h.hyp (t := t) ?_
    (fun K hK K' hK' hz hz' => hU t K hK K' hK' hz hz') J hJ L hL
  intro K hK z hz
  have hzN := hmem K hK z hz
  have htN := hmem J hJ t ht
  have hzo : orderOf (e ⟨z, hzN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hz.sq) hz.ne_one
  have hto : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact ht.sq) ht.ne_one
  obtain ⟨s, hs⟩ := isConj_iff.mp (Walter.psl2_isConj_of_orderOf_eq_two F hFcard
    (hp.odd_of_ne_two hp2) hf1 hzo hto)
  refine ⟨((e.symm s : N) : G), ?_⟩
  have h1 : e.symm s * ⟨z, hzN⟩ * (e.symm s)⁻¹ = ⟨t, htN⟩ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hs]
  exact congrArg Subtype.val h1

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
