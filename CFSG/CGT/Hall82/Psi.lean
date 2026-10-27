module

public import CFSG.CGT.Hall82.Points
public import CFSG.CGT.Hall82.Block
public import CFSG.CGT.Hall82.Cocycle
public import CFSG.CGT.Hall82.ModelFacts
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabCert
public import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import TauCeti.GroupTheory.SemidirectProduct
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G}

theorem card_eq_1080_mul_card_blockQ (S : Setting G M L) : Nat.card L = 1080 * Nat.card (blockQ L) := by
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  rw [S.card_quot] at h2
  have hP : Nat.card (blockQ L) = Nat.card (CFSG.pCore 2 ↥L) := by
    rw [blockQ, CFSG.Open.pCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
  rw [← hP] at h2
  exact h2

theorem pointsHyp (S : Setting G M L) : ∃ z, PointsHyp (blockU L) L z := by
  obtain ⟨z, hzL, hz3, -, hzcent, hfpf⟩ := S.exists_fpf
  have hz3' : z ^ 3 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hz3]
  refine ⟨z, fun a ha b hb => S.blockU_comm ha hb, fun v hv => by simpa [pow_two] using S.blockU_sq hv,
    S.card_blockU, ?_, hzL, hz3', hfpf, hzcent, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [S.normalizer_blockU_eq]
    exact S.le
  · intro s hsL hs5
    by_contra h
    push Not at h
    have hsP : s ∈ blockQ L := S.mem_blockQ_of_forall_conj_eq hsL h
    obtain ⟨n, hn⟩ := S.blockQ_isPGroup ⟨s, hsP⟩
    have hpow : s ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hdvd : orderOf s ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hpow
    rw [hs5] at hdvd
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
    norm_num at h52
  · intro W hWV hWN
    rcases S.short.irreducible W (by rw [S.blockZ_eq_bot]; exact bot_le) hWV hWN with h | h
    · exact Or.inl (by rw [h, S.blockZ_eq_bot])
    · exact Or.inr h
  · exact ⟨216 * Nat.card (blockQ L), by rw [S.card_eq_1080_mul_card_blockQ]; ring⟩
  · intro h25
    obtain ⟨n, hn⟩ := S.blockQ_isPGroup.exists_card_eq
    rw [S.card_eq_1080_mul_card_blockQ, hn] at h25
    have hcop : Nat.Coprime 25 (2 ^ n) := (by norm_num : Nat.Coprime 25 2).pow_right n
    have hd : 25 ∣ 1080 := hcop.dvd_of_dvd_mul_right h25
    norm_num at hd
  · rw [S.card_eq_1080_mul_card_blockQ]
    refine Nat.mul_dvd_mul_left 1080 (Subgroup.card_dvd_of_le ?_)
    intro p hp
    have hp' : p ∈ CFSG.Open.pCoreOf 2 L := hp
    exact Subgroup.mem_inf.mpr ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 L hp',
      Subgroup.mem_centralizer_iff.mpr fun v hv => (S.blockQ_comm_blockU hp hv).symm⟩

theorem exists_hexaCoord (S : Setting G M L) :
    ∃ R rep, HexaCoord (blockU L) R (hallPts (blockU L) L) rep := by
  obtain ⟨z, hz⟩ := S.pointsHyp
  obtain ⟨R, -, rep, hc⟩ :=
    PointsHyp.exists_hexaCoord hz hexaStab_check
  exact ⟨R, rep, hc⟩

variable {R : Subgroup G} {rep : Fin 64 → G}

noncomputable def psiM (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    ↥M →* Equiv.Perm (Fin 64) :=
  hc.psi.comp (Subgroup.inclusion (le_of_eq S.normalizer_blockU_eq.symm))

theorem rep_psiM (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (m : ↥M) (v : Fin 64) :
    rep (S.psiM hc m v) = (m : G) * rep v * (m : G)⁻¹ := by
  simpa [psiM] using
    hc.rep_psi (Subgroup.inclusion (le_of_eq S.normalizer_blockU_eq.symm) m) v

theorem psiM_mem_hexaM (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (m : ↥M) :
    S.psiM hc m ∈ hexaM := by
  have hmem := HexaCoord.psi_mem_hexaM_of_maps hc hexa_check hexaStab_check
    (Subgroup.inclusion (le_of_eq S.normalizer_blockU_eq.symm) m) ?_
  · simpa [psiM] using hmem
  · intro P hP
    have hmV : (m : G) ∈ Subgroup.normalizer (blockU L : Set G) := by
      rw [S.normalizer_blockU_eq]
      exact m.2
    have hmL : (m : G) ∈ Subgroup.normalizer (L : Set G) := by
      rw [S.normalizer_eq]
      exact m.2
    simpa using conj_mem_hallPts hmV hmL hP

theorem psiM_eq_one_iff (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (m : ↥M) :
    S.psiM hc m = 1 ↔ (m : G) ∈ Subgroup.centralizer (blockU L : Set G) := by
  simpa [psiM] using
    hc.psi_eq_one_iff (Subgroup.inclusion (le_of_eq S.normalizer_blockU_eq.symm) m)

noncomputable def psiSub (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (A : Subgroup G) :
    Subgroup (Equiv.Perm (Fin 64)) :=
  (A.subgroupOf M).map (S.psiM hc)

theorem mem_psiSub (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {A : Subgroup G}
    (hA : A ≤ M) {x : Equiv.Perm (Fin 64)} :
    x ∈ S.psiSub hc A ↔ ∃ a ∈ A, ∃ ha : a ∈ M, S.psiM hc ⟨a, ha⟩ = x := by
  rw [psiSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, y.2, by rw [← hyx]⟩
  · rintro ⟨a, ha, haM, rfl⟩
    exact ⟨⟨a, haM⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem psiSub_mono (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {A B : Subgroup G}
    (hAB : A ≤ B) : S.psiSub hc A ≤ S.psiSub hc B := by
  rw [psiSub, psiSub]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono M hAB)

theorem psiSub_le_hexaM (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (A : Subgroup G) :
    S.psiSub hc A ≤ hexaM := by
  rintro x hx
  rw [psiSub, Subgroup.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact S.psiM_mem_hexaM hc y

theorem isPGroup_psiSub (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {A : Subgroup G} {p : ℕ}
    (hA : IsPGroup p A) : IsPGroup p (S.psiSub hc A) := by
  rw [psiSub]
  have h : IsPGroup p (A.subgroupOf M) := by
    intro x
    obtain ⟨n, hn⟩ := hA ⟨(x.1 : G), Subgroup.mem_subgroupOf.mp x.2⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hn
  exact h.map (S.psiM hc)

theorem card_psiSub (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {A : Subgroup G}
    (hA : A ≤ M) :
    Nat.card A = Nat.card ↥(A ⊓ Subgroup.centralizer (blockU L : Set G)) *
      Nat.card (S.psiSub hc A) := by
  let ψA : ↥A →* Equiv.Perm (Fin 64) := (S.psiM hc).comp (Subgroup.inclusion hA)
  have hker : Nat.card ↥ψA.ker =
      Nat.card ↥(A ⊓ Subgroup.centralizer (blockU L : Set G)) := by
    have h1 : ψA = (S.psiM hc).comp (Subgroup.inclusion hA) := rfl
    have hψ : ψA.ker = (Subgroup.centralizer (blockU L : Set G)).comap A.subtype := by
      ext x
      rw [h1, MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.comp_apply]
      exact S.psiM_eq_one_iff hc (Subgroup.inclusion hA x)
    rw [hψ, Subgroup.comap_subtype]
    have hsub : (Subgroup.centralizer (blockU L : Set G)).subgroupOf A =
        (A ⊓ Subgroup.centralizer (blockU L : Set G)).subgroupOf A := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left)).toEquiv
  have hrange : Nat.card ↥ψA.range = Nat.card (S.psiSub hc A) := by
    have h1 : ψA = (S.psiM hc).comp (Subgroup.inclusion hA) := rfl
    have hψ : ψA.range = S.psiSub hc A := by
      rw [h1, MonoidHom.range_comp, Subgroup.inclusion_range, psiSub]
    rw [hψ]
  have h := Subgroup.card_ker_mul_card_range ψA
  rw [hker, hrange] at h
  exact h.symm

theorem conj_rep_eq_iff (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (m : ↥M) (v : Fin 64) :
    (m : G) * rep v * (m : G)⁻¹ = rep v ↔ S.psiM hc m v = v := by
  constructor
  · intro h
    apply hc.inj
    rw [S.rep_psiM hc m v, h]
  · intro h
    rw [← S.rep_psiM hc m v, h]

theorem mem_fixPts_psiSub_iff (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {A : Subgroup G}
    (hA : A ≤ M) (v : Fin 64) :
    v ∈ fixPts (S.psiSub hc A) ↔
      rep v ∈ blockU L ⊓ Subgroup.centralizer (A : Set G) := by
  constructor
  · intro hv
    refine Subgroup.mem_inf.mpr ⟨hc.mem v, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hmem : S.psiM hc ⟨a, hA ha⟩ ∈ S.psiSub hc A := by
      rw [mem_psiSub S hc hA]
      exact ⟨a, ha, hA ha, rfl⟩
    have hfix : S.psiM hc ⟨a, hA ha⟩ v = v := hv _ hmem
    have hp : a * rep v * a⁻¹ = rep v := (conj_rep_eq_iff S hc ⟨a, hA ha⟩ v).mpr hfix
    calc a * rep v = a * rep v * a⁻¹ * a := by group
      _ = rep v * a := by rw [hp]
  · rintro hv x hx
    change x ∈ S.psiSub hc A at hx
    rw [mem_psiSub S hc hA] at hx
    obtain ⟨a, ha, haM, rfl⟩ := hx
    refine (conj_rep_eq_iff S hc ⟨a, haM⟩ v).mp ?_
    have hcomm : a * rep v = rep v * a :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 a ha
    calc a * rep v * a⁻¹ = rep v * a * a⁻¹ := by rw [hcomm]
      _ = rep v := by group

theorem card_inf_centralizer (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {A : Subgroup G}
    (hA : A ≤ M) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card (fixPts (S.psiSub hc A)) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨hc.equiv.symm ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩, ?_⟩
      invFun := fun v => ⟨rep v.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [mem_fixPts_psiSub_iff S hc hA, hc.rep_symm]
    exact x.2
  · exact (mem_fixPts_psiSub_iff S hc hA v.1).mp v.2
  · intro x
    apply Subtype.ext
    exact hc.rep_symm ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩
  · intro v
    apply Subtype.ext
    exact hc.equiv.symm_apply_apply v.1

theorem card_inf_centralizer_singleton (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (m : ↥M) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({(m : G)} : Set G)) =
      Nat.card (fixPts {S.psiM hc m}) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨hc.equiv.symm ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩, ?_⟩
      invFun := fun v => ⟨rep v.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simp only [fixPts, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
    apply (conj_rep_eq_iff S hc m (hc.equiv.symm ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩)).mp
    rw [hc.rep_symm]
    have hcomm : (m : G) * x.1 = x.1 * (m : G) :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2 m (by simp)
    rw [hcomm]
    group
  · refine Subgroup.mem_inf.mpr ⟨hc.mem v.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    have hp : (m : G) * rep v.1 * (m : G)⁻¹ = rep v.1 :=
      (conj_rep_eq_iff S hc m v.1).mpr (by simpa [fixPts] using v.2)
    calc (m : G) * rep v.1 = (m : G) * rep v.1 * (m : G)⁻¹ * (m : G) := by group
      _ = rep v.1 * (m : G) := by rw [hp]
  · intro x
    apply Subtype.ext
    exact hc.rep_symm ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩
  · intro v
    apply Subtype.ext
    exact hc.equiv.symm_apply_apply v.1

theorem inf_centralizer_blockU_eq_blockQ (S : Setting G M L) :
    L ⊓ Subgroup.centralizer (blockU L : Set G) = blockQ L := by
  apply le_antisymm
  · rintro x ⟨hxL, hxV⟩
    refine S.mem_blockQ_of_forall_conj_eq hxL fun v hv => ?_
    have h := Subgroup.mem_centralizer_iff.mp hxV v hv
    calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [h]
      _ = v := by group
  · intro p hp
    refine Subgroup.mem_inf.mpr ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 L hp, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (S.blockQ_comm_blockU hp hv).symm

theorem psiSub_L (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    S.psiSub hc L = hexaL := by
  have hcard : Nat.card (S.psiSub hc L) = 1080 := by
    have h6 := S.card_psiSub hc S.le
    rw [inf_centralizer_blockU_eq_blockQ S, S.card_eq_1080_mul_card_blockQ] at h6
    have hpos : 0 < Nat.card (blockQ L) := Nat.card_pos
    have h6' : 1080 * Nat.card (blockQ L) = Nat.card (S.psiSub hc L) * Nat.card (blockQ L) :=
      calc 1080 * Nat.card (blockQ L) = Nat.card (blockQ L) * Nat.card (S.psiSub hc L) := h6
        _ = Nat.card (S.psiSub hc L) * Nat.card (blockQ L) := mul_comm _ _
    exact (Nat.eq_of_mul_eq_mul_right hpos h6').symm
  exact hF.eq_of_card (S.psiSub hc L) (S.psiSub_le_hexaM hc L) hcard

theorem conj_mem_psiSub (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {N : Subgroup G}
    (hNM : N ≤ M) (hN : ∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N) :
    ∀ a ∈ S.psiSub hc M, ∀ x ∈ S.psiSub hc N, a * x * a⁻¹ ∈ S.psiSub hc N := by
  intro a ha x hx
  rw [mem_psiSub S hc (le_refl M)] at ha
  change x ∈ S.psiSub hc N at hx
  rw [mem_psiSub S hc hNM] at hx
  obtain ⟨m, -, hmM, rfl⟩ := ha
  obtain ⟨n, hn, hnM, rfl⟩ := hx
  rw [mem_psiSub S hc hNM]
  refine ⟨m * n * m⁻¹, hN m hmM n hn,
    M.mul_mem (M.mul_mem hmM hnM) (M.inv_mem hmM), ?_⟩
  have harg : (⟨m * n * m⁻¹, M.mul_mem (M.mul_mem hmM hnM) (M.inv_mem hmM)⟩ : ↥M) =
      ⟨m, hmM⟩ * ⟨n, hnM⟩ * ⟨m, hmM⟩⁻¹ := Subtype.ext rfl
  rw [harg]
  simp only [map_mul, map_inv]

theorem conj_mem_psiSub_of_mem_hexaL (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {N : Subgroup G}
    (hNM : N ≤ M) (hN : ∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N) :
    ∀ a ∈ hexaL, ∀ x ∈ S.psiSub hc N, a * x * a⁻¹ ∈ S.psiSub hc N := by
  have hL := S.psiSub_L hF hc
  intro a ha
  rw [← hL] at ha
  exact S.conj_mem_psiSub hc hNM hN a (S.psiSub_mono hc S.le ha)

theorem centralizer_blockU_eq (S : Setting G M L) :
    Subgroup.centralizer (blockU L : Set G) =
      blockU L ⊔ Subgroup.centralizer (L : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hzL, -, -, hzc, hfpf⟩ := S.exists_fpf
    set D : Subgroup G := blockQ L ⊓ Subgroup.centralizer (L : Set G) with hD
    have hδ : ∀ l ∈ L, ∃ d ∈ D, ∃ v ∈ blockU L, x * l * x⁻¹ * l⁻¹ = d * v := by
      intro l hl
      obtain ⟨hcL, hcV⟩ := S.conj_mem_of_centralizer hx hl
      have hcP : x * l * x⁻¹ * l⁻¹ ∈ blockQ L := by
        refine S.mem_blockQ_of_forall_conj_eq hcL fun v hv => ?_
        have hcomm : v * (x * l * x⁻¹ * l⁻¹) = (x * l * x⁻¹ * l⁻¹) * v :=
          Subgroup.mem_centralizer_iff.mp hcV v hv
        calc (x * l * x⁻¹ * l⁻¹) * v * (x * l * x⁻¹ * l⁻¹)⁻¹
            = v * (x * l * x⁻¹ * l⁻¹) * (x * l * x⁻¹ * l⁻¹)⁻¹ := by rw [hcomm]
          _ = v := by group
      obtain ⟨d, hdD, v, hvV, hdv⟩ := S.exists_mul_of_mem_blockQ hcP
      exact ⟨d, hdD, v, hvV, hdv⟩
    have hDV : D ⊓ blockU L = ⊥ := by
      have h : D ⊓ blockU L ≤ blockU L ⊓ Subgroup.centralizer (L : Set G) := by
        rintro y ⟨hyD, hyV⟩
        exact ⟨hyV, (Subgroup.mem_inf.mp hyD).2⟩
      exact le_bot_iff.mp (h.trans (le_of_eq S.blockZ_eq_bot))
    have hxV : ∀ v ∈ blockU L, x * v * x⁻¹ = v := by
      intro v hv
      have h := Subgroup.mem_centralizer_iff.mp hx v hv
      calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [← h]
        _ = v := by group
    exact mem_sup_of_cocycle
      (fun a ha b hb => S.blockU_comm ha hb)
      (by rw [S.normalizer_blockU_eq]; exact S.le)
      (inf_le_right : D ≤ Subgroup.centralizer (L : Set G))
      (fun a ha b hb => S.blockQ_comm (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp hb).1)
      hDV
      (fun d hd v hv => S.blockQ_comm_blockU (Subgroup.mem_inf.mp hd).1 hv)
      S.perfect hzL hzc hfpf hxV hδ
  · refine sup_le ?_ ?_
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact S.blockU_comm hw hv
    · intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.mp hc v
        (CFSG.LieType.BorelTits.pCoreOf_le 2 L (S.blockU_le_blockQ hv))

theorem blockU_le_pCoreOf (S : Setting G M L) :
    blockU L ≤ CFSG.Open.pCoreOf 2 M := by
  have hV2 : IsPGroup 2 (blockU L) := S.blockQ_isPGroup.to_le S.blockU_le_blockQ
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ hV2
  · exact fun v hv => S.le (CFSG.LieType.BorelTits.pCoreOf_le 2 L (S.blockU_le_blockQ hv))
  · exact le_of_eq S.normalizer_blockU_eq.symm

theorem pCoreOf_centralizer_le (S : Setting G M L) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≤ CFSG.Open.pCoreOf 2 M := by
  have h2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ h2
  · exact (CFSG.LieType.BorelTits.pCoreOf_le 2
      (Subgroup.centralizer (L : Set G))).trans S.centralizer_le
  · have hCM : Subgroup.centralizer (L : Set G) ≤ M := S.centralizer_le
    have hnorm : ((Subgroup.centralizer (L : Set G)).subgroupOf M).Normal := by
      rw [← S.normalizer_eq]
      exact Subgroup.normal_subgroupOf_centralizer_normalizer (L : Set G)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hCM).1 hnorm).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
        (Subgroup.centralizer (L : Set G)))

theorem psiSub_pCoreOf (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    S.psiSub hc (CFSG.Open.pCoreOf 2 M) = ⊥ := by
  apply hF.eq_bot
  · exact S.psiSub_le_hexaM hc _
  · exact S.isPGroup_psiSub hc (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  · refine S.conj_mem_psiSub_of_mem_hexaL hF hc
      (CFSG.LieType.BorelTits.pCoreOf_le 2 M) ?_
    intro m hm y hy
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm) y).mp hy

theorem pCoreOf_le_centralizer (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    CFSG.Open.pCoreOf 2 M ≤ Subgroup.centralizer (blockU L : Set G) := by
  intro j hj
  have hjM : j ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hj
  have h1 : S.psiM hc ⟨j, hjM⟩ = 1 := by
    have hmem : S.psiM hc ⟨j, hjM⟩ ∈ S.psiSub hc (CFSG.Open.pCoreOf 2 M) := by
      rw [mem_psiSub S hc (CFSG.LieType.BorelTits.pCoreOf_le 2 M)]
      exact ⟨j, hj, hjM, rfl⟩
    rwa [S.psiSub_pCoreOf hF hc, Subgroup.mem_bot] at hmem
  exact (S.psiM_eq_one_iff hc ⟨j, hjM⟩).mp h1

theorem pCoreOf_inf_centralizer (S : Setting G M L) :
    CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (L : Set G) =
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
  apply le_antisymm
  · have h2 : IsPGroup 2
        (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_inf_left
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ h2
    intro a ha
    have haM : a ∈ M := S.centralizer_le ha
    have haJ : a ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M haM
    have haC : a ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
      Subgroup.le_normalizer ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxJ, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp haJ x).mp hxJ,
         (Subgroup.mem_normalizer_iff.mp haC x).mp hxC⟩
    · intro hx
      obtain ⟨hxJ, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp haJ x).mpr hxJ,
         (Subgroup.mem_normalizer_iff.mp haC x).mpr hxC⟩
  · exact le_inf S.pCoreOf_centralizer_le
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (Subgroup.centralizer (L : Set G)))

theorem blockU_inf_pCoreOf_centralizer (S : Setting G M L) :
    blockU L ⊓ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) = ⊥ := by
  have h : blockU L ⊓ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≤
      blockU L ⊓ Subgroup.centralizer (L : Set G) :=
    inf_le_inf_left _ (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  exact le_bot_iff.mp (h.trans (le_of_eq S.blockZ_eq_bot))

theorem commute_blockU_pCoreOf_centralizer (S : Setting G M L) {v w : G}
    (hv : v ∈ blockU L)
    (hw : w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) :
    v * w = w * v := by
  have hwL : w ∈ Subgroup.centralizer (L : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw
  have hvL : v ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L (S.blockU_le_blockQ hv)
  exact Subgroup.mem_centralizer_iff.mp hwL v hvL

theorem pCoreOf_eq (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    CFSG.Open.pCoreOf 2 M =
      blockU L ⊔ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
  apply le_antisymm
  · intro j hj
    have hjC : j ∈ Subgroup.centralizer (blockU L : Set G) :=
      S.pCoreOf_le_centralizer hF hc hj
    have hHN : Subgroup.centralizer (L : Set G) ≤
        Subgroup.normalizer (blockU L : Set G) := by
      rw [S.normalizer_blockU_eq]
      exact S.centralizer_le
    have hmod := Subgroup.inf_sup_assoc_of_le (K := CFSG.Open.pCoreOf 2 M)
      (H := Subgroup.centralizer (L : Set G)) (N := blockU L) hHN
      (S.blockU_le_pCoreOf)
    have hJ : (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L =
        CFSG.Open.pCoreOf 2 M := by
      rw [hmod, sup_comm, ← S.centralizer_blockU_eq,
        inf_eq_left.mpr (S.pCoreOf_le_centralizer hF hc)]
    have hJW : blockU L ⊔
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) =
        CFSG.Open.pCoreOf 2 M := by
      rw [sup_comm, ← S.pCoreOf_inf_centralizer, hJ]
    rw [hJW]
    exact hj
  · exact sup_le S.blockU_le_pCoreOf S.pCoreOf_centralizer_le

theorem le_pCoreOf_of_le_centralizer (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    {X : Subgroup G} (hX : IsPGroup 2 X) (hXM : X ≤ M)
    (hXV : X ≤ Subgroup.centralizer (blockU L : Set G)) :
    X ≤ CFSG.Open.pCoreOf 2 M := by
  have hV2 : IsPGroup 2 (blockU L) := S.blockQ_isPGroup.to_le S.blockU_le_blockQ
  have hXVN : X ≤ Subgroup.normalizer (blockU L : Set G) := by
    rw [S.normalizer_blockU_eq]
    exact hXM
  set Y : Subgroup G := X ⊔ blockU L with hYdef
  have hY2 : IsPGroup 2 Y := by
    rw [hYdef]
    exact IsPGroup.to_sup_of_normal_right' hX hV2 hXVN
  have hYV : Y ≤ Subgroup.centralizer (blockU L : Set G) := by
    rw [hYdef]
    refine sup_le hXV ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact S.blockU_comm hw hv
  have hHN : Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (blockU L : Set G) := by
    rw [S.normalizer_blockU_eq]
    exact S.centralizer_le
  have hYeq : (Y ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L = Y := by
    have h := Subgroup.inf_sup_assoc_of_le (K := Y)
      (H := Subgroup.centralizer (L : Set G)) (N := blockU L) hHN le_sup_right
    rw [h, sup_comm, ← S.centralizer_blockU_eq, inf_eq_left.mpr hYV]
  have hQW : Y ⊓ Subgroup.centralizer (L : Set G) ≤
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) :=
    hW2 _ (IsPGroup.to_inf_left hY2) inf_le_right
  have hYJ : Y ≤ CFSG.Open.pCoreOf 2 M := by
    rw [← hYeq, S.pCoreOf_eq hF hc]
    exact sup_le (hQW.trans le_sup_right) le_sup_left
  exact le_trans le_sup_left hYJ

theorem mem_pCoreOf_of_commute (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {k : G}
    (hk : k ∈ Subgroup.centralizer (L : Set G))
    (hkW : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), k * w = w * k) :
    k ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
  have hkM : k ∈ M := S.centralizer_le hk
  have hkV : ∀ v ∈ blockU L, k * v = v * k := by
    intro v hv
    have hvL : v ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L (S.blockU_le_blockQ hv)
    exact (Subgroup.mem_centralizer_iff.mp hk v hvL).symm
  have hkJ : ∀ j ∈ CFSG.Open.pCoreOf 2 M, k * j = j * k := by
    intro j hj
    have hj' : j ∈ (blockU L ⊔
        CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) : Subgroup G) := by
      rw [← S.pCoreOf_eq hF hc]
      exact hj
    have hWN : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≤
        Subgroup.normalizer (blockU L : Set G) := by
      rw [S.normalizer_blockU_eq]
      exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans S.centralizer_le
    obtain ⟨v, hv, w, hw, hvw⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := blockU L) hWN).mp hj'
    rw [hvw]
    calc k * (v * w) = (k * v) * w := by group
      _ = (v * k) * w := by rw [hkV v hv]
      _ = v * (k * w) := by group
      _ = v * (w * k) := by rw [hkW w hw]
      _ = (v * w) * k := by group
  have hkCJ : k ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hkJ j hj).symm
  have htwo : CFSG.Open.IsTwoLocal M := S.maxLocal.1
  have hchar := S.charTwo M htwo
  have hkJmem : k ∈ CFSG.Open.pCoreOf 2 M :=
    hchar (Subgroup.mem_inf.mpr ⟨hkM, hkCJ⟩)
  rw [← S.pCoreOf_inf_centralizer]
  exact Subgroup.mem_inf.mpr ⟨hkJmem, hk⟩

noncomputable def M1 (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) : Subgroup G :=
  (hexaL.comap (S.psiM hc)).map M.subtype

theorem mem_M1 (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {x : G} :
    x ∈ S.M1 hc ↔ ∃ hx : x ∈ M, S.psiM hc ⟨x, hx⟩ ∈ hexaL := by
  rw [M1, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hx : x ∈ M := by rw [← hyx]; exact y.2
    refine ⟨hx, ?_⟩
    have hy' : (⟨x, hx⟩ : ↥M) = y := Subtype.ext hyx.symm
    rwa [hy']
  · rintro ⟨hx, hmem⟩
    exact ⟨⟨x, hx⟩, hmem, rfl⟩

theorem M1_le (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) : S.M1 hc ≤ M := by
  rw [M1]
  exact Subgroup.map_subtype_le _

theorem M1_eq (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    S.M1 hc = L ⊔ Subgroup.centralizer (L : Set G) := by
  apply le_antisymm
  · intro x hx
    rw [mem_M1 S hc] at hx
    obtain ⟨hxM, hxL⟩ := hx
    have hxpsi : S.psiM hc ⟨x, hxM⟩ ∈ S.psiSub hc L := by
      rwa [S.psiSub_L hF hc]
    rw [mem_psiSub S hc S.le] at hxpsi
    obtain ⟨l, hlL, hlM, hlpsi⟩ := hxpsi
    have hmem : l * x⁻¹ ∈ M := M.mul_mem hlM (M.inv_mem hxM)
    have hprodmul : (⟨l, hlM⟩ * ⟨x, hxM⟩⁻¹ : ↥M) = ⟨l * x⁻¹, hmem⟩ :=
      Subtype.ext rfl
    have h1 : S.psiM hc ⟨l, hlM⟩ * (S.psiM hc ⟨x, hxM⟩)⁻¹ = 1 := by
      rw [hlpsi]
      group
    have hm_l : S.psiM hc ⟨l * x⁻¹, hmem⟩ = 1 := by
      rw [← hprodmul, map_mul, map_inv]
      exact h1
    have hC : l * x⁻¹ ∈ Subgroup.centralizer (blockU L : Set G) :=
      (S.psiM_eq_one_iff hc ⟨l * x⁻¹, hmem⟩).mp hm_l
    have hCV : l * x⁻¹ ∈
        (blockU L ⊔ Subgroup.centralizer (L : Set G) : Subgroup G) := by
      rw [← S.centralizer_blockU_eq]
      exact hC
    have hHN : Subgroup.centralizer (L : Set G) ≤
        Subgroup.normalizer (blockU L : Set G) := by
      rw [S.normalizer_blockU_eq]
      exact S.centralizer_le
    obtain ⟨v, hvV, c₀, hc₀C, hvc⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := blockU L) hHN).mp hCV
    have hVL : blockU L ≤ L := fun w hw =>
      CFSG.LieType.BorelTits.pCoreOf_le 2 L (S.blockU_le_blockQ hw)
    have hxeq : x = c₀⁻¹ * (v⁻¹ * l) := by
      have h1 : l * x⁻¹ = v * c₀ := hvc
      calc x = (l * x⁻¹)⁻¹ * l := by group
        _ = (v * c₀)⁻¹ * l := by rw [h1]
        _ = c₀⁻¹ * (v⁻¹ * l) := by group
    rw [hxeq]
    have hmem : c₀⁻¹ * (v⁻¹ * l) ∈
        Subgroup.centralizer (L : Set G) ⊔ L := by
      refine Subgroup.mul_mem_sup ?_ ?_
      · exact (Subgroup.centralizer (L : Set G)).inv_mem hc₀C
      · exact L.mul_mem (L.inv_mem (hVL hvV)) hlL
    rwa [sup_comm] at hmem
  · refine sup_le ?_ ?_
    · intro l hl
      rw [mem_M1 S hc]
      have hmem : S.psiM hc ⟨l, S.le hl⟩ ∈ S.psiSub hc L := by
        rw [mem_psiSub S hc S.le]
        exact ⟨l, hl, S.le hl, rfl⟩
      exact ⟨S.le hl, by rwa [S.psiSub_L hF hc] at hmem⟩
    · intro c hcL
      rw [mem_M1 S hc]
      have hcM : c ∈ M := S.centralizer_le hcL
      refine ⟨hcM, ?_⟩
      have h1 : S.psiM hc ⟨c, hcM⟩ = 1 := by
        rw [S.psiM_eq_one_iff hc]
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact Subgroup.mem_centralizer_iff.mp hcL v
          (CFSG.LieType.BorelTits.pCoreOf_le 2 L (S.blockU_le_blockQ hv))
      rw [h1]
      exact hexaL.one_mem

theorem index_M1 (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    ((S.M1 hc).subgroupOf M).index ∣ 2 := by
  have hK : (S.M1 hc).subgroupOf M = hexaL.comap (S.psiM hc) := by
    rw [← Subgroup.map_subtype_inj (H := M)]
    rw [Subgroup.map_subgroupOf_eq_of_le (S.M1_le hc)]
    rfl
  rw [hK]
  have hψr : hexaL.comap (S.psiM hc) =
      (hexaL.subgroupOf (S.psiM hc).range).comap (S.psiM hc).rangeRestrict := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl
  have hidx : (hexaL.comap (S.psiM hc)).index =
      (hexaL.subgroupOf (S.psiM hc).range).index := by
    rw [hψr]
    exact Subgroup.index_comap_of_surjective
      (hexaL.subgroupOf (S.psiM hc).range)
      (f := (S.psiM hc).rangeRestrict) (S.psiM hc).rangeRestrict_surjective
  rw [hidx]
  have hrange_le : (S.psiM hc).range ≤ hexaM := by
    rintro x ⟨m, rfl⟩
    exact S.psiM_mem_hexaM hc m
  have hhexa_le_range : hexaL ≤ (S.psiM hc).range := by
    rw [← S.psiSub_L hF hc]
    intro x hx
    have hmono : S.psiSub hc L ≤ S.psiSub hc M := S.psiSub_mono hc S.le
    have hx' : x ∈ S.psiSub hc M := hmono hx
    rwa [psiSub, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at hx'
  have hcard : Nat.card ↥(S.psiM hc).range =
      (hexaL.subgroupOf (S.psiM hc).range).index *
        Nat.card ↥(hexaL.subgroupOf (S.psiM hc).range) := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcard1080 : Nat.card ↥(hexaL.subgroupOf (S.psiM hc).range) = 1080 := by
    rw [← hF.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hhexa_le_range).toEquiv
  have hdvd : Nat.card ↥(S.psiM hc).range ∣ 2160 := by
    simpa [hF.card_hexaM] using Subgroup.card_dvd_of_le hrange_le
  rw [hcard, hcard1080] at hdvd
  have hdvd' : (hexaL.subgroupOf (S.psiM hc).range).index * 1080 ∣ 2 * 1080 := by
    rwa [show 2 * 1080 = 2160 from by norm_num]
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hdvd'

end CFSG.CGT.Hall82.Setting

