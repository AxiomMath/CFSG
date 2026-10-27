module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactL34FixedPoints
public import Certificates.Certificate9461
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Transitive
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.ComponentClassification.PSL3Four
open CFSG.PSL3Four.Native
open CFSG.ABGLocalTools

namespace KFactL34FixedPointsProof

theorem nonempty_mulEquiv_S {L : Type} [Group L]
    (h : Nonempty (L ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 2))) : Nonempty (L ≃* S) := by
  obtain ⟨e⟩ := h
  obtain ⟨eS⟩ := classicalModel_S.2
  exact ⟨e.trans eS.symm⟩

theorem exists_conj_eq_z0
    {z₀ : Equiv.Perm (Fin 42)} (hz₀S : z₀ ∈ S)
    (hz₀3 : z₀ ^ 3 = 1) (hz₀1 : z₀ ≠ 1) {z : Equiv.Perm (Fin 42)} (hzS : z ∈ S)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : ∃ s ∈ S, s * z * s⁻¹ = z₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let zS : S := ⟨z, hzS⟩
  let z₀S : S := ⟨z₀, hz₀S⟩
  have hzS1 : zS ≠ 1 := by intro h; exact hz1 (congrArg Subtype.val h)
  have hz₀S1 : z₀S ≠ 1 := by intro h; exact hz₀1 (congrArg Subtype.val h)
  have hzS3 : zS ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hz3
  have hz₀S3 : z₀S ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hz₀3
  have hPz : IsPGroup 3 (Subgroup.zpowers zS) := by
    have hcard : Nat.card (Subgroup.zpowers zS) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hzS3 hzS1]
    exact IsPGroup.of_card (n := 1) (by simp [hcard])
  have hP₀ : IsPGroup 3 (Subgroup.zpowers z₀S) := by
    have hcard : Nat.card (Subgroup.zpowers z₀S) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz₀S3 hz₀S1]
    exact IsPGroup.of_card (n := 1) (by simp [hcard])
  obtain ⟨Tz, hPzTz⟩ := IsPGroup.exists_le_sylow hPz
  obtain ⟨T₀, hP₀T₀⟩ := IsPGroup.exists_le_sylow hP₀
  have hfac : (Nat.card S).factorization 3 = 2 := by
    rw [card_S, Nat.factorization_def _ Nat.prime_three,
      show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hTzcard : Nat.card (Tz : Subgroup S) = 9 := by
    rw [Sylow.card_eq_multiplicity, hfac]
    norm_num
  have hT₀card : Nat.card (T₀ : Subgroup S) = 9 := by
    rw [Sylow.card_eq_multiplicity, hfac]
    norm_num
  have hTzsyl : IsSylowOf 3 (Tz : Subgroup S) ⊤ := by
    refine isSylowOf_of_card le_top ?_
    rw [Subgroup.card_top, hfac, hTzcard]
    norm_num
  have hT₀syl : IsSylowOf 3 (T₀ : Subgroup S) ⊤ := by
    refine isSylowOf_of_card le_top ?_
    rw [Subgroup.card_top, hfac, hT₀card]
    norm_num
  obtain ⟨k, -, hk⟩ := hT₀syl.exists_mem_conj hTzsyl
  have hzTz : zS ∈ (Tz : Subgroup S) := hPzTz (Subgroup.mem_zpowers zS)
  have hz'T₀ : k⁻¹ * zS * k ∈ (T₀ : Subgroup S) := (hk zS).1 hzTz
  have hz'1 : k⁻¹ * zS * k ≠ 1 := by
    intro h
    apply hzS1
    calc zS = k * (k⁻¹ * zS * k) * k⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hz'3 : (k⁻¹ * zS * k) ^ 3 = 1 := by
    calc (k⁻¹ * zS * k) ^ 3 = k⁻¹ * zS ^ 3 * k := by
          rw [pow_three, pow_three]; group
      _ = 1 := by rw [hzS3]; group
  obtain ⟨eS⟩ := classicalModel_S.2
  obtain ⟨n, -, hnconj⟩ := exists_mem_normalizer_conj_eq eS hT₀card
    (a := k⁻¹ * zS * k) (b := z₀S) hz'T₀ (by simpa using hz'1)
    (hP₀T₀ (Subgroup.mem_zpowers z₀S)) (by simpa using hz₀S1)
  refine ⟨((n : S) * k⁻¹ : S), ((n : S) * k⁻¹ : S).2, ?_⟩
  exact congrArg Subtype.val (by
    calc (n : S) * k⁻¹ * zS * ((n : S) * k⁻¹)⁻¹
        = (n : S) * (k⁻¹ * zS * k) * (n : S)⁻¹ := by group
      _ = z₀S := hnconj)

theorem card_inf_ge_three {F' : Subgroup R}
    (hcard : Nat.card F' = 9) (hnot : ¬ F' ≤ S.subgroupOf R) :
    3 ≤ Nat.card (F' ⊓ S.subgroupOf R : Subgroup R) := by
  haveI : (S.subgroupOf R).Normal := S_normal
  have hSR : Nat.card (S.subgroupOf R) = 20160 := by
    rw [← card_S]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe S_le_R).toEquiv
  have hquot : Nat.card (R ⧸ S.subgroupOf R) = 12 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (S.subgroupOf R)
    rw [card_R, hSR] at h
    omega
  let q : F' →* R ⧸ S.subgroupOf R := (QuotientGroup.mk' (S.subgroupOf R)).comp F'.subtype
  have hcardq : Nat.card q.ker * Nat.card q.range = 9 := by
    rw [Subgroup.card_ker_mul_card_range q, hcard]
  have hq12 : Nat.card q.range ∣ 12 := by
    have h := Subgroup.card_subgroup_dvd_card (q.range : Subgroup (R ⧸ S.subgroupOf R))
    rwa [hquot] at h
  have hq9 : Nat.card q.range ∣ 9 := ⟨Nat.card q.ker, by rw [mul_comm, hcardq]⟩
  have hq3 : Nat.card q.range ∣ 3 := by
    have h := Nat.dvd_gcd hq9 hq12
    simpa using h
  have hker3 : 3 ≤ Nat.card q.ker := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hq3 with h1 | h3
    · rw [h1] at hcardq; omega
    · rw [h3] at hcardq; omega
  have hker : q.ker = (F' ⊓ S.subgroupOf R).subgroupOf F' := by
    ext x
    simp only [MonoidHom.mem_ker, q, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have hx' : (QuotientGroup.mk' (S.subgroupOf R)) (x : R) = 1 := by simpa using hx
      rw [QuotientGroup.mk'_apply] at hx'
      exact ⟨x.2, (QuotientGroup.eq_one_iff (x : R)).mp hx'⟩
    · rintro ⟨-, hxS⟩
      have hx' : (QuotientGroup.mk (x : R) : R ⧸ S.subgroupOf R) = 1 :=
        (QuotientGroup.eq_one_iff (x : R)).mpr hxS
      simpa [q, QuotientGroup.mk'_apply] using hx'
  have hHcard : Nat.card (F' ⊓ S.subgroupOf R : Subgroup R) = Nat.card q.ker := by
    rw [hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  omega

end KFactL34FixedPointsProof

open KFactL34FixedPointsProof

theorem kFactL34FixedPointsGen :
    KFactL34FixedPointsGen := by
  intro L _ _ hL F hF hFcard hout Y hY
  obtain ⟨ε⟩ := nonempty_mulEquiv_S hL
  obtain ⟨φ, hφ, hφS⟩ := full_automorphism_action
  let ψ : MulAut L ≃* R := (MulAut.congr ε).trans φ.symm
  let F' : Subgroup R := F.map ψ.toMonoidHom
  have hψφ : ∀ f : MulAut L, φ (ψ f) = MulAut.congr ε f := by
    intro f; simp [ψ]
  have hF'card : Nat.card F' = 9 := by
    change Nat.card (F.map ψ.toMonoidHom) = 9
    rw [Subgroup.card_map_of_injective ψ.injective, hFcard]
  have hF'el : CFSG.Open.IsElemAbelian 3 F' := by
    change CFSG.Open.IsElemAbelian 3 (F.map ψ.toMonoidHom)
    exact hF.map ψ.toMonoidHom
  have hF'notle : ¬ F' ≤ S.subgroupOf R := by
    intro hle
    have hmap : F'.map ψ.symm.toMonoidHom ≤ (MulAut.conj : L →* MulAut L).range := by
      calc F'.map ψ.symm.toMonoidHom ≤ (S.subgroupOf R).map ψ.symm.toMonoidHom :=
            Subgroup.map_mono hle
        _ ≤ (MulAut.conj : L →* MulAut L).range := by
            intro f hf
            obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hf
            have hφr : φ r ∈ (MulAut.conj : S →* MulAut S).range := by
              rw [← hφS]
              exact Subgroup.mem_map_of_mem φ.toMonoidHom hr
            obtain ⟨s, hs⟩ := hφr
            refine ⟨ε.symm s, ?_⟩
            have h1 : ψ.symm r = (MulAut.congr ε).symm (φ r) := by simp [ψ]
            have h2 : (MulAut.congr ε) (MulAut.conj (ε.symm s)) = MulAut.conj s := by
              ext t
              simp [MulAut.congr_apply, MulAut.conj_apply]
            have h3 : (MulAut.congr ε).symm (MulAut.conj s) = MulAut.conj (ε.symm s) := by
              rw [← h2, MulEquiv.symm_apply_apply]
            change MulAut.conj (ε.symm s) = ψ.symm r
            rw [h1, ← hs, h3]
    have hFmap : F'.map ψ.symm.toMonoidHom = F := by
      change (F.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = F
      rw [Subgroup.map_map]
      simp
    rw [hFmap] at hmap
    exact hout hmap
  have hHcard : 3 ≤ Nat.card (F' ⊓ S.subgroupOf R : Subgroup R) :=
    card_inf_ge_three hF'card hF'notle
  let H : Subgroup R := F' ⊓ S.subgroupOf R
  have hHcard' : 3 ≤ Nat.card H := hHcard
  haveI : Fintype H := Fintype.ofFinite H
  haveI : Nontrivial H := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨zH, hzHne⟩ := exists_ne (1 : H)
  let zR : R := (zH : R)
  have hzF' : zR ∈ F' := (zH : H).2.1
  have hzSR : zR ∈ S.subgroupOf R := (zH : H).2.2
  have hzS : (zR : Equiv.Perm (Fin 42)) ∈ S := Subgroup.mem_subgroupOf.mp hzSR
  have hzR1 : zR ≠ 1 := by
    intro h1
    exact hzHne (Subtype.ext h1)
  have hzR3 : zR ^ 3 = 1 := hF'el.2 zR hzF'
  have hz3 : (zR : Equiv.Perm (Fin 42)) ^ 3 = 1 := by
    simpa using congrArg (fun r : R => (r : Equiv.Perm (Fin 42))) hzR3
  have hz1 : (zR : Equiv.Perm (Fin 42)) ≠ 1 := by
    intro h1
    exact hzR1 (Subtype.ext h1)
  have hx_exists : ∃ xR ∈ F', xR ∉ S.subgroupOf R := by
    by_contra h
    exact hF'notle fun xR hxR => by
      by_contra hxSR
      exact h ⟨xR, hxR, hxSR⟩
  obtain ⟨xR, hxF', hxSR⟩ := hx_exists
  have hxS : (xR : Equiv.Perm (Fin 42)) ∉ S := hxSR
  have hxR1 : xR ≠ 1 := by
    intro h1
    exact hxSR (by rw [h1]; exact (S.subgroupOf R).one_mem)
  have hxR3 : xR ^ 3 = 1 := hF'el.2 xR hxF'
  have hx3 : (xR : Equiv.Perm (Fin 42)) ^ 3 = 1 := by
    simpa using congrArg (fun r : R => (r : Equiv.Perm (Fin 42))) hxR3
  have hcommR : xR * zR = zR * xR := by
    have h := hF'el.1.is_comm.comm ⟨xR, hxF'⟩ ⟨zR, hzF'⟩
    simpa using congrArg (fun r : F' => (r : R)) h
  have hcommPerm : (xR : Equiv.Perm (Fin 42)) * (zR : Equiv.Perm (Fin 42)) =
      (zR : Equiv.Perm (Fin 42)) * (xR : Equiv.Perm (Fin 42)) := by
    simpa using congrArg (fun r : R => (r : Equiv.Perm (Fin 42))) hcommR
  let zxR : R := zR * xR
  let z2xR : R := zR * zR * xR
  have hzxF' : zxR ∈ F' := F'.mul_mem hzF' hxF'
  have hz2xF' : z2xR ∈ F' := F'.mul_mem (F'.mul_mem hzF' hzF') hxF'
  have hzx1 : zxR ≠ 1 := by
    intro h1
    change zR * xR = 1 at h1
    apply hxSR
    have hx_eq : xR = zR⁻¹ := by
      calc xR = zR⁻¹ * (zR * xR) := by group
        _ = zR⁻¹ * 1 := by rw [h1]
        _ = zR⁻¹ := by group
    rw [hx_eq]
    exact (S.subgroupOf R).inv_mem hzSR
  have hz2x1 : z2xR ≠ 1 := by
    intro h1
    change zR * zR * xR = 1 at h1
    apply hxSR
    have hx_eq : xR = (zR * zR)⁻¹ := by
      calc xR = (zR * zR)⁻¹ * (zR * zR * xR) := by group
        _ = (zR * zR)⁻¹ * 1 := by rw [h1]
        _ = (zR * zR)⁻¹ := by group
    rw [hx_eq]
    exact (S.subgroupOf R).inv_mem ((S.subgroupOf R).mul_mem hzSR hzSR)
  obtain ⟨z₀, hz₀S, hz₀3, hz₀1, hgen⟩ := Certificates.certificate9461
  obtain ⟨s, hsS, hsz⟩ := exists_conj_eq_z0 hz₀S hz₀3 hz₀1 hzS hz3 hz1
  let Y' : Subgroup S := Y.map ε.toMonoidHom
  let Yp : Subgroup (Equiv.Perm (Fin 42)) := Y'.map S.subtype
  have hfixed_mem : ∀ fR ∈ F', fR ≠ 1 → ∀ c (hcS : c ∈ S),
      φ fR ⟨c, hcS⟩ = ⟨c, hcS⟩ → c ∈ Yp := by
    intro fR hfR hfR1 c hcS hfix
    obtain ⟨f, hfF, hfψ⟩ := Subgroup.mem_map.mp hfR
    have hf1 : f ≠ 1 := by
      intro h1
      apply hfR1
      rw [← hfψ, h1, map_one]
    let l : L := ε.symm ⟨c, hcS⟩
    have hcl : ε l = ⟨c, hcS⟩ := ε.apply_symm_apply _
    have hfl : f l = l := by
      apply ε.injective
      have hfψ' : ψ f = fR := by simpa using hfψ
      have h' : (MulAut.congr ε f) (ε l) = ε l := by
        have hfix' : φ (ψ f) ⟨c, hcS⟩ = ⟨c, hcS⟩ := by
          rw [hfψ']; exact hfix
        rw [hψφ, ← hcl] at hfix'
        exact hfix'
      have h2 : (MulAut.congr ε f) (ε l) = ε (f l) := by
        rw [MulAut.congr_apply]
        simp
      rw [h2] at h'
      exact h'
    have hlY : l ∈ Y := hY f hfF hf1 l hfl
    have hcY' : (⟨c, hcS⟩ : S) ∈ Y' := by
      have hmem : ε l ∈ Y' := Subgroup.mem_map_of_mem ε.toMonoidHom hlY
      rwa [hcl] at hmem
    exact Subgroup.mem_map_of_mem S.subtype hcY'
  have mem_Yp_of_comm : ∀ (r : R), r ∈ F' → r ≠ 1 → ∀ c ∈ S,
      c * (r : Equiv.Perm (Fin 42)) = (r : Equiv.Perm (Fin 42)) * c → c ∈ Yp := by
    intro r hrF hr1 c hcS hcomm
    apply hfixed_mem r hrF hr1 c hcS
    apply Subtype.ext
    rw [hφ r ⟨c, hcS⟩]
    calc (r : Equiv.Perm (Fin 42)) * c * (r : Equiv.Perm (Fin 42))⁻¹
        = c * (r : Equiv.Perm (Fin 42)) * (r : Equiv.Perm (Fin 42))⁻¹ := by rw [hcomm]
      _ = c := by group
  have hCent_z : ∀ c ∈ S, c * (zR : Equiv.Perm (Fin 42)) =
      (zR : Equiv.Perm (Fin 42)) * c → c ∈ Yp :=
    fun c hcS h => mem_Yp_of_comm zR hzF' hzR1 c hcS h
  have hCent_x : ∀ c ∈ S, c * (xR : Equiv.Perm (Fin 42)) =
      (xR : Equiv.Perm (Fin 42)) * c → c ∈ Yp :=
    fun c hcS h => mem_Yp_of_comm xR hxF' hxR1 c hcS h
  have hCent_zx : ∀ c ∈ S, c * ((zR : Equiv.Perm (Fin 42)) * (xR : Equiv.Perm (Fin 42))) =
      ((zR : Equiv.Perm (Fin 42)) * (xR : Equiv.Perm (Fin 42))) * c → c ∈ Yp := by
    intro c hcS h
    exact mem_Yp_of_comm zxR hzxF' hzx1 c hcS (by simpa [zxR] using h)
  have hCent_z2x : ∀ c ∈ S,
      c * ((zR : Equiv.Perm (Fin 42)) ^ 2 * (xR : Equiv.Perm (Fin 42))) =
        ((zR : Equiv.Perm (Fin 42)) ^ 2 * (xR : Equiv.Perm (Fin 42))) * c → c ∈ Yp := by
    intro c hcS h
    exact mem_Yp_of_comm z2xR hz2xF' hz2x1 c hcS (by simpa [z2xR, pow_two] using h)
  let x' : Equiv.Perm (Fin 42) := s * (xR : Equiv.Perm (Fin 42)) * s⁻¹
  have hx'R : x' ∈ R :=
    R.mul_mem (R.mul_mem (S_le_R hsS) xR.2) (R.inv_mem (S_le_R hsS))
  have hx'3 : x' ^ 3 = 1 := by
    have h3 : x' ^ 3 = s * ((xR : Equiv.Perm (Fin 42)) ^ 3) * s⁻¹ := by
      dsimp only [x']
      rw [pow_three, pow_three]
      group
    rw [h3, hx3]
    group
  have hx'z0 : x' * z₀ = z₀ * x' := by
    have hz0 : z₀ = s * (zR : Equiv.Perm (Fin 42)) * s⁻¹ := hsz.symm
    calc x' * z₀ = s * ((xR : Equiv.Perm (Fin 42)) * (zR : Equiv.Perm (Fin 42))) * s⁻¹ := by
          rw [hz0]; simp only [x']; group
      _ = s * ((zR : Equiv.Perm (Fin 42)) * (xR : Equiv.Perm (Fin 42))) * s⁻¹ := by
          rw [hcommPerm]
      _ = z₀ * x' := by rw [hz0]; simp only [x']; group
  have hx'notS : x' ∉ S := by
    intro h
    exact hxS (conj_mem_S' (S_le_R hsS) (by simpa [x'] using h))
  have hsz_rev : s⁻¹ * z₀ * s = (zR : Equiv.Perm (Fin 42)) := by
    rw [← hsz]; group
  have hx_rev : s⁻¹ * x' * s = (xR : Equiv.Perm (Fin 42)) := by
    simp [x']; group
  have hzx_rev : s⁻¹ * (z₀ * x') * s =
      (zR : Equiv.Perm (Fin 42)) * (xR : Equiv.Perm (Fin 42)) := by
    rw [show z₀ = s * (zR : Equiv.Perm (Fin 42)) * s⁻¹ from hsz.symm]
    simp only [x']; group
  have hz2x_rev : s⁻¹ * (z₀ ^ 2 * x') * s =
      (zR : Equiv.Perm (Fin 42)) ^ 2 * (xR : Equiv.Perm (Fin 42)) := by
    rw [show z₀ = s * (zR : Equiv.Perm (Fin 42)) * s⁻¹ from hsz.symm]
    simp only [x', pow_two]; group
  let Y'' : Subgroup (Equiv.Perm (Fin 42)) := Yp.map (MulAut.conj s).toMonoidHom
  have step : ∀ {c r' r : Equiv.Perm (Fin 42)}, c ∈ S → s⁻¹ * r' * s = r →
      c * r' = r' * c → (∀ d ∈ S, d * r = r * d → d ∈ Yp) → c ∈ Y'' := by
    intro c r' r hcS hr' hc hCent
    let d : Equiv.Perm (Fin 42) := s⁻¹ * c * s
    have hdS : d ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hsS) hcS) hsS
    have hdcomm : d * r = r * d := by
      calc d * r = s⁻¹ * c * (s * r) := by simp [d]; group
        _ = s⁻¹ * c * (s * (s⁻¹ * r' * s)) := by rw [← hr']
        _ = s⁻¹ * (c * r') * s := by group
        _ = s⁻¹ * (r' * c) * s := by rw [hc]
        _ = (s⁻¹ * r' * s) * d := by simp [d]; group
        _ = r * d := by rw [← hr']
    have hdYp : d ∈ Yp := hCent d hdS hdcomm
    have hcd : s * d * s⁻¹ = c := by simp [d]; group
    have hmem : (MulAut.conj s) d ∈ Y'' := Subgroup.mem_map_of_mem (MulAut.conj s).toMonoidHom hdYp
    rwa [show (MulAut.conj s) d = c by simpa [MulAut.conj_apply] using hcd] at hmem
  have hY''cent : ∀ c ∈ S, c * z₀ = z₀ * c ∨ c * x' = x' * c ∨
      c * (z₀ * x') = z₀ * x' * c ∨ c * (z₀ ^ 2 * x') = z₀ ^ 2 * x' * c → c ∈ Y'' := by
    intro c hcS h
    rcases h with h | h | h | h
    · exact step hcS hsz_rev h hCent_z
    · exact step hcS hx_rev h hCent_x
    · exact step hcS hzx_rev h hCent_zx
    · exact step hcS hz2x_rev h hCent_z2x
  have hSleY'' : S ≤ Y'' := hgen x' hx'R hx'3 hx'z0 hx'notS Y'' hY''cent
  have hmapS : S.map (MulAut.conj s).toMonoidHom = S := by
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using conj_mem_S (S_le_R hsS) hy
    · intro hx
      refine ⟨s⁻¹ * x * s, ?_, ?_⟩
      · exact conj_mem_S (R.inv_mem (S_le_R hsS)) hx
      · simp [MulAut.conj_apply]; group
  have hmapS_inv : S.map (MulAut.conj s).symm.toMonoidHom = S := by
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_symm_apply] using conj_mem_S (R.inv_mem (S_le_R hsS)) hy
    · intro hx
      refine ⟨s * x * s⁻¹, ?_, ?_⟩
      · exact conj_mem_S (S_le_R hsS) hx
      · simp [MulAut.conj_symm_apply]; group
  have hY''map : Y''.map (MulAut.conj s).symm.toMonoidHom = Yp := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hy
      have hx' : x = d := by
        rw [← hyx, ← hdy]
        exact MulEquiv.symm_apply_apply _ _
      rwa [hx']
    · intro x hx
      exact ⟨(MulAut.conj s) x, Subgroup.mem_map_of_mem _ hx,
        MulEquiv.symm_apply_apply _ _⟩
  have hSleYp : S ≤ Yp := by
    have h := Subgroup.map_mono (f := (MulAut.conj s).symm.toMonoidHom) hSleY''
    rwa [hmapS_inv, hY''map] at h
  have hYp_le_S : Yp ≤ S := Subgroup.map_subtype_le Y'
  have hYp_eq : Yp = S := le_antisymm hYp_le_S hSleYp
  have hY'card : Nat.card Y' = Nat.card Yp := by
    change Nat.card Y' = Nat.card (Y'.map S.subtype)
    exact (Subgroup.card_map_of_injective S.subtype_injective).symm
  have hY'eq : Y' = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [hY'card, hYp_eq, Subgroup.card_top]
  have hYmap : Y.map ε.toMonoidHom = ⊤ := hY'eq
  ext l
  constructor
  · intro _; exact Subgroup.mem_top _
  · intro _
    have hmem : ε l ∈ Y.map ε.toMonoidHom := by rw [hYmap]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
    rw [← ε.injective hyeq]
    exact hy

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
