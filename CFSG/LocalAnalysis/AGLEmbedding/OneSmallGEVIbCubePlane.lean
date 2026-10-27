module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroBase
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltBasic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem le_of_pow_two_dvd_factorial {p n : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ n.factorial) :
    p ≤ n :=
  (Nat.Prime.dvd_factorial hp).mp ((dvd_pow_self p (by norm_num)).trans h)

theorem pow_two_dvd_card_alternatingGroup {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (h : p ^ 2 ∣ n.factorial) : p ^ 2 ∣ Nat.card (alternatingGroup (Fin n)) := by
  rw [← two_mul_card_alternatingGroup_fin hn] at h
  exact Nat.Coprime.dvd_of_dvd_mul_left
    (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_left 2) h

theorem false_of_quotient_perm_two {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y} {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hJ : IbPerfectSections p J)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) (hdvd : p ^ 2 ∣ Nat.card J) : False := by
  have h1 := pow_dvd_card_quotient_pCore_two hp (by omega) hdvd
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin] at h1
  have hn := le_of_pow_two_dvd_factorial hp h1
  have h5 : 5 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  exact not_dvd_card_of_surjective_of_perfect hJ
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (alternatingGroup (Fin n))
    (commutator_alternatingGroup_eq_self h5)
    (pow_two_dvd_card_alternatingGroup hp (by omega) (by omega) h1)

theorem false_of_quotient_perm_prod_two {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y}
    {p r m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hJ : IbPerfectSections p J)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* (Equiv.Perm (Fin r) × Equiv.Perm (Fin m)))
    (hdvd : p ^ 2 ∣ Nat.card J) : False := by
  have hp2 : p ≠ 2 := by omega
  have h1 := pow_dvd_card_quotient_pCore_two hp hp2 hdvd
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm,
    Nat.card_eq_fintype_card (α := Fin r), Nat.card_eq_fintype_card (α := Fin m),
    Fintype.card_fin, Fintype.card_fin] at h1
  set ψ := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
  have hs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcop : ∀ k : ℕ, k < p → (p ^ 2).Coprime k.factorial := fun k hk =>
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
      absurd ((Nat.Prime.dvd_factorial hp).mp h) (by omega))
  rcases Nat.lt_or_ge r p with hr | hr
  · have h2 : p ^ 2 ∣ m.factorial := Nat.Coprime.dvd_of_dvd_mul_left (hcop r hr) h1
    have hm := le_of_pow_two_dvd_factorial hp h2
    have h5 : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    exact not_dvd_card_of_surjective_of_perfect hJ ((MonoidHom.snd _ _).comp ψ)
      (Prod.snd_surjective.comp hs) (alternatingGroup (Fin m))
      (commutator_alternatingGroup_eq_self h5)
      (pow_two_dvd_card_alternatingGroup hp hp2 (by omega) h2)
  rcases Nat.lt_or_ge m p with hm | hm
  · have h2 : p ^ 2 ∣ r.factorial := Nat.Coprime.dvd_of_dvd_mul_right (hcop m hm) h1
    have h5 : 5 ≤ Nat.card (Fin r) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    exact not_dvd_card_of_surjective_of_perfect hJ ((MonoidHom.fst _ _).comp ψ)
      (Prod.fst_surjective.comp hs) (alternatingGroup (Fin r))
      (commutator_alternatingGroup_eq_self h5)
      (pow_two_dvd_card_alternatingGroup hp hp2 (by omega) h2)
  have h5r : 5 ≤ Nat.card (Fin r) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  have h5m : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  refine not_dvd_card_of_surjective_of_perfect hJ ψ hs
    ((alternatingGroup (Fin r)).prod (alternatingGroup (Fin m))) ?_ ?_
  · rw [Subgroup.commutator_prod_prod, commutator_alternatingGroup_eq_self h5r,
      commutator_alternatingGroup_eq_self h5m]
  · rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
    have hpr : p ∣ Nat.card (alternatingGroup (Fin r)) := by
      have := (Nat.Prime.dvd_factorial hp).mpr hr
      rw [← two_mul_card_alternatingGroup_fin (by omega : 2 ≤ r)] at this
      exact (Nat.Prime.dvd_mul hp).mp this |>.resolve_left fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hpm : p ∣ Nat.card (alternatingGroup (Fin m)) := by
      have := (Nat.Prime.dvd_factorial hp).mpr hm
      rw [← two_mul_card_alternatingGroup_fin (by omega : 2 ≤ m)] at this
      exact (Nat.Prime.dvd_mul hp).mp this |>.resolve_left fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    rw [pow_two]
    exact mul_dvd_mul hpr hpm

theorem not_pow_two_dvd_of_five_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ 1080 ∧ ¬ p ^ 2 ∣ 2520 := by
  have key : ∀ n : ℕ, n ≤ 2520 → p ^ 2 ∣ n → n ≠ 0 → p ≤ 50 := by
    intro n hn h hn0
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h
    by_contra h50
    have : 51 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := key 1080 (by norm_num) h (by norm_num)
    interval_cases p <;> revert hp h <;> norm_num
  · have := key 2520 (by norm_num) h (by norm_num)
    interval_cases p <;> revert hp h <;> norm_num

variable {G : Type} [Group G] [Finite G]

namespace D1IbCubeConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem mkM_inj (hc : D1IbCubeConfig p P M H R Rbar K z) {a b : G} (ha : a ∈ R) (hb : b ∈ R)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, hc.phase.le_M ha⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hc.phase.le_M hb⟩) : a = b :=
  congrArg Subtype.val (eq_of_mk_eq_of_isPGroup hc.prime (CFSG.pCore 2 ↥M) hc.coprime_twoCore
    hc.phase.isPGroup.comap_subtype (Subgroup.mem_subgroupOf.mpr ha)
    (Subgroup.mem_subgroupOf.mpr hb) h)

theorem elem_center (hc : D1IbCubeConfig p P M H R Rbar K z) (hShape : KFactSmallSylowShape) :
    IsElemAbelian p (centerOf (d1LiftX p H R K) ⊔ Subgroup.zpowers z) ∧
      Nat.card (centerOf (d1LiftX p H R K) ⊔ Subgroup.zpowers z : Subgroup G) = p ^ 2 ∧
      centerOf (d1LiftX p H R K) ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer (R : Set G) := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set T := d1LiftX p H R K
  set Z₀ := centerOf T
  set E' := Z₀ ⊔ Subgroup.zpowers z
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hE'R : E' ≤ R := sup_le (inf_le_left.trans hTR) (Subgroup.zpowers_le.mpr hc.elt.1)
  have hE'C : E' ≤ Subgroup.centralizer (R : Set G) := by
    refine sup_le (fun c hcZ => Subgroup.mem_centralizer_iff.mpr fun r hr =>
      (hc.centerOf_le_centralizer hcZ hr).symm) (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_iff.mpr fun r hr => hc.commute_z hr))
  have hzp : orderOf z = p := hc.elt.2.1
  have hinf : Z₀ ⊓ Subgroup.zpowers z = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    by_contra hy1
    exact hc.card_d1LiftX.2 ((Subgroup.zpowers_le.mpr hy.1.1)
      (mem_zpowers_of_mem_zpowers_of_prime hp hzp hy.2 hy1))
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => hc.exp g (hE'R hg)⟩, ?_, hE'C⟩
  · exact (Subgroup.mem_centralizer_iff.mp (hE'C a.2) b (hE'R b.2)).symm
  · have hlow := mul_card_le_of_inf_eq_bot (le_sup_left : Z₀ ≤ E') le_sup_right hinf
    rw [hc.card_Z hShape, Nat.card_zpowers, hzp] at hlow
    have hdec' : ∀ e : E', ∃ c : Z₀, ∃ y : Subgroup.zpowers z, (e : G) = c * y := by
      intro e
      obtain ⟨c, hcZ, i, he⟩ := hc.central_decomp (hE'R e.2)
        (fun r hr => (Subgroup.mem_centralizer_iff.mp (hE'C e.2) r hr).symm)
      exact ⟨⟨c, hcZ⟩, ⟨z ^ i, Subgroup.npow_mem_zpowers z i⟩, he⟩
    choose f g hfg using hdec'
    have hinj : Function.Injective (fun e : E' => (f e, g e)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      apply Subtype.ext
      rw [hfg a, hfg b, hab.1, hab.2]
    have hup := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hc.card_Z hShape, Nat.card_zpowers, hzp] at hup
    rw [pow_two]
    exact le_antisymm hup hlow

theorem false_of_plane (hc : D1IbCubeConfig p P M H R Rbar K z) (hI : D1IbCubeInputs)
    (hShape : KFactSmallSylowShape) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZL : centerOf (d1LiftX p H R K) ≤ rPart M R (barM M L))
    (hzL : z ∈ rPart M R (barM M L)) : False := by
  have hp := hc.prime
  have hp5 := hc.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hB := hI.blocks
  have hRM := hc.phase.le_M
  set T := d1LiftX p H R K
  set Z₀ := centerOf T
  set E' := Z₀ ⊔ Subgroup.zpowers z
  obtain ⟨hE'el, hE'card, hE'C⟩ := hc.elem_center hShape
  have hE'L : E' ≤ rPart M R (barM M L) := sup_le hZL (Subgroup.zpowers_le.mpr hzL)
  have hE'R : E' ≤ R := hE'L.trans inf_le_left
  obtain ⟨x, hxP, hxN, -, hxz⟩ := hc.data.exists_moving_elt hc.elt hc.b0
  have hxM : x ∈ M := hc.phase.normalizer_le hxN
  have hxE' : ∀ g ∈ E', x * g * x⁻¹ ∈ E' := by
    intro g hg
    have hgR := hE'R hg
    have hxg : x * g * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxN g).mp hgR
    have hcent : ∀ r ∈ R, x * g * x⁻¹ * r = r * (x * g * x⁻¹) := by
      intro r hr
      have hr' : x⁻¹ * r * x ∈ R := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) r).mp hr
        simpa using this
      have h1 : (x⁻¹ * r * x) * g = g * (x⁻¹ * r * x) :=
        Subgroup.mem_centralizer_iff.mp (hE'C hg) _ hr'
      calc x * g * x⁻¹ * r = x * (g * (x⁻¹ * r * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * r * x) * g) * x⁻¹ := by rw [h1]
        _ = r * (x * g * x⁻¹) := by group
    obtain ⟨c, hcZ, i, hci⟩ := hc.central_decomp hxg hcent
    rw [hci]
    exact E'.mul_mem (Subgroup.mem_sup_left hcZ)
      (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers z i))
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set zb := mkM ⟨z, hc.mem_M⟩
  set Lb := barM M L
  set PL := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)
  set E := barM M E'
  set y := mkM ⟨x, hxM⟩
  obtain ⟨hEel, hEcard'⟩ := hc.barM_elem hE'R hE'el
  have hEcard : Nat.card E = p ^ 2 := hEcard'.trans hE'card
  have hEL : E ≤ Lb := by
    rintro _ ⟨r, hr, rfl⟩
    have hrR := hE'R (Subgroup.mem_subgroupOf.mp hr)
    exact (mem_rPart hRM hrR).mp (hE'L (Subgroup.mem_subgroupOf.mp hr))
  have hzbL : zb ∈ Lb := (mem_rPart hRM hc.elt.1).mp hzL
  have hEC : E ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
      (hc.le_centralizer (hE'R (Subgroup.mem_subgroupOf.mp hr)))))
  have hzE : zb ∈ E := ⟨⟨z, hc.mem_M⟩,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)), rfl⟩
  have hyE : y ∈ Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    obtain ⟨m, hm, rfl⟩ := he
    have hmE := Subgroup.mem_subgroupOf.mp hm
    refine ⟨⟨x, hxM⟩ * m * ⟨x, hxM⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · simpa using hxE' m hmE
    · simp only [map_mul, map_inv]
      rfl
  have hyp : ∃ k : ℕ, y ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
    refine ⟨k, ?_⟩
    have : (⟨x, hxM⟩ : ↥M) ^ p ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [← map_pow, this, map_one]
  have hwR : x * z * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxN z).mp hc.elt.1
  have hwE : x * z * x⁻¹ ∈ E' := hxE' z (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hyz : y * zb * y⁻¹ = mkM ⟨x * z * x⁻¹, hRM hwR⟩ := by
    simp only [y, zb, ← map_mul, ← map_inv]
    rfl
  have hyL : y ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    set L' := Lb.map (MulAut.conj y).toMonoidHom
    have hL' : IsComponentOf L' ⊤ :=
      (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj y) Lb).mpr hL.component
    have hmem : mkM ⟨x * z * x⁻¹, hRM hwR⟩ ∈ L' :=
      ⟨zb, hzbL, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hyz⟩
    have hne : L' = Lb := by
      by_contra hne
      have h1 := le_centralizer_of_component_ne hL' hL.component hne hmem
      have h2 : x * z * x⁻¹ ∈ rPart M R
          (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
        (mem_rPart hRM hwR).mpr h1
      have h3 := hc.le_d1LiftX_of_not_mem hShape hI.orbits inf_le_left (hc.isInvR_cent hL)
        (hc.not_mem_cent hL) h2
      exact hc.conj_not_mem hShape hxN h3
    refine Subgroup.mem_normalizer_fintype fun l hl => ?_
    have : y * l * y⁻¹ ∈ L' := ⟨l, hl, by simp [MulAut.conj_apply]⟩
    rwa [hne] at this
  have hyzb : y * zb * y⁻¹ ≠ zb := by
    rw [hyz]
    intro h
    have := hc.mkM_inj hwR hc.elt.1 h
    exact hxz (by rw [this]; exact Subgroup.mem_zpowers z)
  have hEP : E ≤ PL := fun e he => hc.zbar_fixed_le L e (hEL he) (by
    show zb * e * zb⁻¹ = e
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEC he), mul_inv_cancel_right])
  have hPLs := hc.perf_block hL
  have hdvdP : p ^ 2 ∣ Nat.card PL := hEcard ▸ Subgroup.card_dvd_of_le hEP
  have hdvdL : p ^ 2 ∣ Nat.card Lb := hEcard ▸ Subgroup.card_dvd_of_le hEL
  have hn1 := hc.phase.nineThree_not_one hB.h85 hB.hD2 hL
  rcases hc.phase.nineThree hB.h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hn1.1
  · obtain ⟨V, hVp, hVL, hVO, hzV⟩ := hc.exists_cover_block hL
    have hVO' : V ≤ Subgroup.normalizer (pCoreOf 2 PL : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [← h2.2.2]
      exact hVO
    exact hyzb (hI.plane _ Lb PL hL.component h2.1 h2.2.1 (hc.phase.barM_ne_of_isWeakSBlock hL)
      (ne_inf_normalizer_of_nineThreeTwo h2 (hn1.2 h2)) p hp hp5 hPLs zb hzbL hc.zbar_pow
      (hc.zbar_not_mem_centralizer hL) ⟨V, hVp, hVL, hVO', hzV⟩ (hc.zbar_fixed_le L)
      E (le_inf hEL hEC) hEel hEcard hzE y hyL hyE hyp zb hzE)
  · exact hI.three G M (pCoreOf 2 H) L p hc.phase.isKGroup.1 hc.phase.asc81bHyp hL hn1.1
      (hc.phase.not_isSylowTwoOf_inf hB.h85 hB.hD2 hL) h3 hp hp5 hPLs E hEP hEel hEcard
  · obtain ⟨-, hZ, ⟨e⟩, -⟩ := h4
    have hcard : Nat.card Lb = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Lb), hZ,
        Nat.card_congr e.toEquiv]
      have := two_mul_card_alternatingGroup_fin (n := 6) (by norm_num)
      rw [show Nat.factorial 6 = 720 by rfl] at this
      omega
    exact (not_pow_two_dvd_of_five_le hp hp5).1 (hcard ▸ hdvdL)
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    have hcard : Nat.card Lb = 2520 := by
      rw [Nat.card_congr e.toEquiv]
      have := two_mul_card_alternatingGroup_fin (n := 7) (by norm_num)
      rw [show Nat.factorial 7 = 5040 by rfl] at this
      omega
    exact (not_pow_two_dvd_of_five_le hp hp5).2 (hcard ▸ hdvdL)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact false_of_quotient_perm_two hp hp5 hPLs e hdvdP
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact false_of_quotient_perm_two hp hp5 hPLs e hdvdP
  · obtain ⟨-, N, r, -, -, -, -, -, -, φ, -⟩ := h8
    exact false_of_quotient_perm_prod_two hp hp5 hPLs φ hdvdP

end D1IbCubeConfig

end CFSG.AGLEmbedding
