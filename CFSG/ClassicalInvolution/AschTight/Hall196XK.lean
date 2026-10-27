module

public import CFSG.ClassicalInvolution.AschTight.Hall196QD
public import CFSG.ClassicalInvolution.AschTight.Hall196XG
public import CFSG.ClassicalInvolution.AschTight.Hall196Idx2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem sec19X_le_normalizer (hd : Sec19Data p f K z S W) :
    sec19X K z ≤ Subgroup.normalizer (K : Set G) :=
  (gammaGen_le_centralizer _ z).trans (normalizer_eq_centralizer_of_tight hd.tight.toTightBranch).ge

theorem normal_subgroupOf_sec19X (hd : Sec19Data p f K z S W) :
    (K.subgroupOf (sec19X K z)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (S1916.le_sec19X hd.tight.branch.member)).mpr
    (sec19X_le_normalizer hd)

theorem sec19X_le_normalizer_sup (hd : Sec19Data p f K z S W) :
    sec19X K z ≤ Subgroup.normalizer ((K ⊔ sec19Y K z : Subgroup G) : Set G) := by
  intro x hx
  have hxK := sec19X_le_normalizer hd hx
  have hxY : x ∈ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G) :=
    centralizer_le_normalizer_sec19Y hd.tight (gammaGen_le_centralizer _ z hx)
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  calc conjSub x (K ⊔ sec19Y K z) = conjSub x K ⊔ conjSub x (sec19Y K z) := Subgroup.map_sup _ _ _
    _ = K ⊔ sec19Y K z := by
      rw [conjSub_eq_of_mem_normalizer hxK, conjSub_eq_of_mem_normalizer hxY]

theorem index_map_sup_sec19Y [IsSimpleGroup G] (hd : Sec19Data p f K z S W)
    [(K.subgroupOf (sec19X K z)).Normal] :
    (((K ⊔ sec19Y K z).subgroupOf (sec19X K z)).map
        (QuotientGroup.mk' (K.subgroupOf (sec19X K z)))).index = 2 ∧
      (((K ⊔ sec19Y K z).subgroupOf (sec19X K z)).map
        (QuotientGroup.mk' (K.subgroupOf (sec19X K z)))).Normal ∧
      ((K ⊔ sec19Y K z).subgroupOf (sec19X K z)).map
          (QuotientGroup.mk' (K.subgroupOf (sec19X K z))) =
        ((sec19Y K z).subgroupOf (sec19X K z)).map
          (QuotientGroup.mk' (K.subgroupOf (sec19X K z))) := by
  have hKX : K ≤ sec19X K z := S1916.le_sec19X hd.tight.branch.member
  have hYX : sec19Y K z ≤ sec19X K z := sec19Y_le_sec19X K z
  have hs := QuotientGroup.mk'_surjective (K.subgroupOf (sec19X K z))
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.index_map, QuotientGroup.ker_mk', MonoidHom.range_eq_top.mpr hs,
      Subgroup.index_top, mul_one, sup_eq_left.mpr (fun x hx =>
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))]
    exact relIndex_sup_sec19Y hd
  · have : ((K ⊔ sec19Y K z).subgroupOf (sec19X K z)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hKX hYX)).mpr
        (sec19X_le_normalizer_sup hd)
    exact Subgroup.Normal.map inferInstance _ hs
  · rw [Subgroup.subgroupOf_sup hKX hYX, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]

theorem eq_top_of_normal_of_odd_index_sec19X_quot [(K.subgroupOf (sec19X K z)).Normal]
    (M : Subgroup (↥(sec19X K z) ⧸ K.subgroupOf (sec19X K z))) (hM : M.Normal)
    (hodd : Odd M.index) : M = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (K.subgroupOf (sec19X K z)) with hπ
  have hs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set M' := M.comap π with hM'
  have : M'.Normal := hM.comap π
  have hodd' : Odd M'.index := by rwa [hM', Subgroup.index_comap_of_surjective M hs]
  have hX : sec19X K z ≤ M'.map (sec19X K z).subtype := by
    refine iSup₂_le fun A hA => ?_
    have hAX : A ≤ sec19X K z := le_iSup₂ (f := fun (B : Subgroup G)
      (_ : (B ∈ USet (CoreAssembly.conjClass K) ∨ B ∈ RSet (CoreAssembly.conjClass K)) ∧
        B ≤ Subgroup.centralizer ({z} : Set G)) => B) A hA
    have hA2 : IsPGroup 2 A := by
      rcases hA.1 with hU | hR
      · obtain ⟨R', hR', hAR', -, -⟩ := hU
        exact (isPGroup_of_mem_rSet hR').to_le hAR'
      · exact isPGroup_of_mem_rSet hR
    have hle : A.subgroupOf (sec19X K z) ≤ M' :=
      le_of_isPGroup_of_odd_index hodd' hA2.comap_subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hAX]
    exact Subgroup.map_mono hle
  have htop : M' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hX x.2
    rw [← Subtype.ext hyx]
    exact hy
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := hs x
  have hy : y ∈ M' := htop ▸ Subgroup.mem_top y
  exact hy

theorem hasDihedralSylowTwo_sec19X_quot [IsSimpleGroup G] (hstar : C19_11aTmp p f)
    (hDT : Sec19DataT p f K z S W L t V)
    (hQ : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)) [(K.subgroupOf (sec19X K z)).Normal] :
    CFSG.GorensteinWalter.HasDihedralSylowTwo (↥(sec19X K z) ⧸ K.subgroupOf (sec19X K z)) ∧
      8 ∣ Nat.card (↥(sec19X K z) ⧸ K.subgroupOf (sec19X K z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hDT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  obtain ⟨q, hqP, -, hq2, hqt, -, -, hcardP⟩ := exists_quat_elem hstar hDT hQ
  obtain ⟨-, -, -, hVcyc, -⟩ := hDT.memV
  obtain ⟨v₀, hv₀⟩ := hVcyc.exists_generator
  have hvo : orderOf (v₀ : G) = Nat.card V := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hv₀]
  have hYX : sec19Y K z ≤ sec19X K z := sec19Y_le_sec19X K z
  have hv₀X : (v₀ : G) ∈ sec19X K z := S1911.le_sec19X hd (hDT.leW v₀.2)
  have hqX : q ∈ sec19X K z := hYX hqP.2
  set π := QuotientGroup.mk' (K.subgroupOf (sec19X K z)) with hπ
  have hπ1 : ∀ x : ↥(sec19X K z), π x = 1 ↔ (x : G) ∈ K := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set ρ := π ⟨v₀, hv₀X⟩ with hρ
  set σ := π ⟨q, hqX⟩ with hσ
  have hKV := inf_eq_bot_of_sec19DataT hDT
  have hρo : orderOf ρ = Nat.card V := by
    rw [← hvo, ← Subgroup.orderOf_mk (v₀ : G) hv₀X, orderOf_eq_orderOf_iff]
    intro n
    rw [hρ, ← map_pow, hπ1]
    constructor
    · intro h
      have h2 : (v₀ : G) ^ n ∈ K ⊓ V := ⟨by simpa using h, V.pow_mem v₀.2 n⟩
      rw [hKV, Subgroup.mem_bot] at h2
      exact Subtype.ext (by simpa using h2)
    · intro h
      rw [h]
      exact K.one_mem
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσ, ← map_pow, hπ1, sq]
    show q * q ∈ K
    rw [hq2]
    exact hI.mem
  have hK1 : q * v₀ * q⁻¹ * v₀ ∈ K := by
    have h1 := mul_conj_mem_of_quat hDT hqP hq2 hqt v₀.2
    have hv₀N := le_normalizer_of_sec19DataT hDT v₀.2
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hv₀N) _).mp h1
    have e : (v₀ : G)⁻¹ * ((v₀ : G) * (q * v₀ * q⁻¹)) * (v₀ : G)⁻¹⁻¹ = q * v₀ * q⁻¹ * v₀ := by
      group
    rwa [e] at h2
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    have h : σ * ρ * σ⁻¹ * ρ = 1 := by
      rw [hσ, hρ, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hπ1]
      simpa using hK1
    exact eq_inv_of_mul_eq_one_left h
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le (hDT.leW.trans hd.hWS)
  obtain ⟨k, hk⟩ := hV2.exists_card_eq
  have hV4 : 4 ≤ Nat.card V := ef.four
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right two_pos (by omega)
    omega
  obtain ⟨eD⟩ := nonempty_mulEquiv_dihedral (D := Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) rfl hσ2
    hrel (by omega)
  have hcardD : Nat.card ↥(Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) = 2 * Nat.card V := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, hρo]
  have hD2 : IsPGroup 2 ↥(Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) :=
    IsPGroup.of_card (n := k + 1) (by rw [hcardD, hk, pow_succ, mul_comm])
  have hSY : (S : Subgroup G) ≤ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G) :=
    hd.hSz.trans (centralizer_le_normalizer_sec19Y hd.tight)
  have hP := isSylow2In_inf_of_le_normalizer S hSY
  have hPsyl := isSylow2In_map_hom π (isSylow2In_subgroupOf_of_le hP hYX)
  obtain ⟨hNidx, hNn, hNY⟩ := index_map_sup_sec19Y hd
  rw [← hNY] at hPsyl
  have hPX : (S : Subgroup G) ⊓ sec19Y K z ≤ sec19X K z := inf_le_right.trans hYX
  have hPcard : 2 * Nat.card ↥((((S : Subgroup G) ⊓ sec19Y K z).subgroupOf (sec19X K z)).map π) ≤
      Nat.card ↥(Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) := by
    rw [hcardD]
    have h1 := Subgroup.card_ker_mul_card_range
      (π.comp (((S : Subgroup G) ⊓ sec19Y K z).subgroupOf (sec19X K z)).subtype)
    rw [MonoidHom.range_comp, Subgroup.range_subtype,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hcardP, ef.card] at h1
    have hzP : z ∈ (S : Subgroup G) ⊓ sec19Y K z := ⟨S1916.sd_mem_S hd, S1916.sd_mem_Y hd⟩
    have h2 : 2 ≤ Nat.card
        (π.comp (((S : Subgroup G) ⊓ sec19Y K z).subgroupOf (sec19X K z)).subtype).ker := by
      apply (Subgroup.one_lt_card_iff_ne_bot _).mpr
      intro hbot
      have hmem : (⟨⟨z, hPX hzP⟩, Subgroup.mem_subgroupOf.mpr hzP⟩ :
          ↥(((S : Subgroup G) ⊓ sec19Y K z).subgroupOf (sec19X K z))) ∈
          (π.comp (((S : Subgroup G) ⊓ sec19Y K z).subgroupOf (sec19X K z)).subtype).ker :=
        (hπ1 _).mpr hI.mem
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hI.ne_one (congrArg (fun x : ↥(((S : Subgroup G) ⊓ sec19Y K z).subgroupOf
        (sec19X K z)) => ((x : ↥(sec19X K z)) : G)) hmem)
    nlinarith
  have hsyl := isSylow2In_top_of_index_two hNidx hPsyl hD2 hPcard
  rw [hρo, hk] at eD
  refine ⟨hasDihedralSylowTwo_of_isSylow2In hsyl (by omega) eD, ?_⟩
  have h8 : 8 ∣ Nat.card ↥(Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) := by
    rw [hcardD, hk]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    exact ⟨2 ^ j, by ring⟩
  exact h8.trans (Subgroup.card_subgroup_dvd_card _)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
