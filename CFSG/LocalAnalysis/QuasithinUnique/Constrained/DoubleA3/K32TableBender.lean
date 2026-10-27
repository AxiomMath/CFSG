module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBenderOut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableFam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBenderGen

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.GH74.Uniqueness.Bender (BenderType)

variable {K : Type} [Group K] [Finite K]

theorem k32_bender_core
    (hX : fusionIsBenderGroup K) {q k : ℕ} (hB : fusionBenderBorel K q k)
    {X P R A V : Subgroup (MulAut K)} (hd : K32Datum K X P R A V) (hVJ : V ≤ innAut K) :
    ∃ c ∈ A, orderOf c = 3 ∧ (∀ v ∈ V, v ≠ 1 → c * v * c⁻¹ ≠ v) ∧
      (∀ s ∈ P ⊓ innAut K, c * s * c⁻¹ ∈ P ⊓ innAut K) ∧
      (∀ s ∈ P ⊓ innAut K, c⁻¹ * s * c ∈ P ⊓ innAut K) ∧
      IsSylowTwoOf (P ⊓ innAut K) (innAut K) ∧ V ≤ P ⊓ innAut K ∧
      twoPart (innAut K) ≤
        8 * Nat.card ↥((P ⊓ innAut K) ⊓ Subgroup.centralizer ({c} : Set (MulAut K))) := by
  have hXJ : X ≤ Subgroup.normalizer ((innAut K : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.normalizer_eq_top (innAut K)]
    exact le_top
  have hPJ : IsSylowTwoOf (P ⊓ innAut K) (innAut K) :=
    A4.isSylowTwoOf_inf_normal hd.sylow hd.inn_le hXJ
  obtain ⟨c, hcA, hc3, hcN, hcfp, -⟩ := hd.a4.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hVS : V ≤ P ⊓ innAut K := le_inf (hd.V_le.trans hd.R_le) hVJ
  obtain ⟨⟨v, hvV⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot V).mp (by rw [hd.a4.card_U]; norm_num))
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hcvV : c * v * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hcN v).mp hvV
  have hcS : ∀ s ∈ P ⊓ innAut K, c * s * c⁻¹ ∈ P ⊓ innAut K :=
    k32_bender_ti hX hB hPJ c (hVS hvV) hv1' (hVS hcvV)
  have hcc : c * c = c⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hc3')
  have hcS' : ∀ s ∈ P ⊓ innAut K, c⁻¹ * s * c ∈ P ⊓ innAut K := by
    intro s hs
    have h2 := hcS _ (hcS s hs)
    have e : c * (c * s * c⁻¹) * c⁻¹ = c⁻¹ * s * c := by
      calc c * (c * s * c⁻¹) * c⁻¹ = (c * c) * s * (c * c)⁻¹ := by group
        _ = c⁻¹ * s * c := by rw [hcc]; group
    rwa [e] at h2
  exact ⟨c, hcA, hc3, hcfp, hcS, hcS', hPJ, hVS, k32_datum_bound hd hcA hcS⟩

theorem k32_noDatum_bender_nonabelian
    (hX : fusionIsBenderGroup K) {q k : ℕ}
    (hB : fusionBenderBorel K q k) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hOut : ∀ S : Sylow 2 (MulAut K ⧸ innAut K), IsCyclic S)
    {X P R A V : Subgroup (MulAut K)} (hd : K32Datum K X P R A V) : False := by
  have hVJ : V ≤ innAut K := k32_V_le_of_cyclic_sylow hd.a4 hOut
  obtain ⟨c, hcA, hc3, hfp, hcS, hcS', hPJ, hVS, hbound⟩ := k32_bender_core hX hB hd hVJ
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  set S := P ⊓ innAut K with hSdef
  have hZc : ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set (MulAut K)), ∀ s ∈ S, z * s = s * z :=
    fun z hz s hs => (Subgroup.mem_centralizer_iff.mp hz.2 s hs).symm
  have hcZ : ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set (MulAut K)),
      c * z * c⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set (MulAut K)) := by
    intro z hz
    have hmem : c * z * c⁻¹ ∈ Subgroup.centralizer (S : Set (MulAut K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hs' : c⁻¹ * s * c ∈ S := hcS' s hs
      have h1 : (c⁻¹ * s * c) * z = z * (c⁻¹ * s * c) :=
        Subgroup.mem_centralizer_iff.mp hz.2 _ hs'
      calc s * (c * z * c⁻¹) = c * ((c⁻¹ * s * c) * z) * c⁻¹ := by group
        _ = c * (z * (c⁻¹ * s * c)) * c⁻¹ := by rw [h1]
        _ = (c * z * c⁻¹) * s := by group
    exact ⟨hcS z hz.1, hmem⟩
  have hVZ : V ≤ S ⊓ Subgroup.centralizer (S : Set (MulAut K)) := by
    intro v hv
    have hmem : v ∈ Subgroup.centralizer (S : Set (MulAut K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hv2 : v * v = 1 := by rw [← pow_two]; exact hd.a4.sq_U v hv
      exact (k32_bender_sq_central hX hB hq hPJ (hVS hv) hv2 s hs).symm
    exact ⟨hVS hv, hmem⟩
  have hZcomm : S ⊓ Subgroup.centralizer (S : Set (MulAut K)) ≤ ⁅S, S⁆ := fun z hz =>
    k32_bender_center_le_commutator hX hB hPJ (k32_bender_nonabelian hX hB hq hk hPJ) z hz.1
      (fun s hs => (Subgroup.mem_centralizer_iff.mp hz.2 s hs).symm)
  have hphi := k32_phi16 (S := S) (Z := S ⊓ Subgroup.centralizer (S : Set (MulAut K))) (V := V)
    (c := c) hPJ.2.1 inf_le_left hZc hc3' hcS hcZ hVZ hd.a4.card_U hfp hZcomm
  have hS := hPJ.card_eq
  omega

theorem k32_noDatum_bender_psl2
    (hX : fusionIsBenderGroup K) {n : ℕ} (hT : BenderType K n 1 1)
    (hn : 3 ≤ n) {X P R A V : Subgroup (MulAut K)} (hd : K32Datum K X P R A V) : False := by
  obtain ⟨hcyc, hcard⟩ := k32_out_linear hT
  have hB := k32_borel_of_benderType hT
  have hXJ : X ≤ Subgroup.normalizer ((innAut K : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.normalizer_eq_top (innAut K)]
    exact le_top
  have hPJ : IsSylowTwoOf (P ⊓ innAut K) (innAut K) :=
    A4.isSylowTwoOf_inf_normal hd.sylow hd.inn_le hXJ
  by_cases hn3 : n = 3
  ·
    have hodd : Odd (Nat.card (MulAut K ⧸ innAut K)) := by rw [hcard, hn3]; decide
    have hPJ' : P ≤ innAut K := k32_le_of_odd_quot hd.sylow.2.1 hodd
    have hab := k32_psl2_abelian hX hT hPJ
    apply hd.moves
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hrP : r ∈ P := hd.R_le hr
    exact hab v ⟨hd.R_le (hd.V_le hv), hPJ' (hd.R_le (hd.V_le hv))⟩ r ⟨hrP, hPJ' hrP⟩
  · have hn4 : 4 ≤ n := by omega
    have hAJ : A ≤ innAut K := k32_A_le_of_comm hd.a4 (hd.sylow.2.1.to_le hd.R_le) hd.R_norm
      hd.R_normV hd.moves (k32_comm_mem_of_isCyclic hcyc)
    have hVJ : V ≤ innAut K := hd.a4.le.trans hAJ
    obtain ⟨c, hcA, hc3, hfp, hcS, hcS', hPJ2, hVS, hbound⟩ := k32_bender_core hX hB hd hVJ
    have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
    have hc1 : c ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hc3
      omega
    have hfpt := k32_psl2_fpf hX hT hPJ2 (hAJ hcA) hc3' hc1 hcS hcS'
    rw [hfpt, Subgroup.card_bot] at hbound
    have hS := k32_card_sylow_inn hX hT hPJ2
    have hS2 := hPJ2.card_eq
    have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    rw [pow_one] at hS
    omega

theorem k32ExclBender_proved
    : K32ExclBender := by
  intro K _ _ hq hX hne X P R A V hd
  obtain ⟨n, i, e, hT⟩ := k32_benderType hX
  have hB := k32_borel_of_benderType hT
  have hn2 : 2 ≤ n := by
    rcases hT.cases' with ⟨-, -, hn⟩ | ⟨-, -, a, ha, hna⟩ | ⟨-, -, hn⟩
    · exact hn
    · omega
    · exact hn
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hT.cases' with ⟨hi, he, -⟩ | ⟨hi, he, -, -, -⟩ | ⟨hi, he, -⟩
  · subst hi
    subst he
    by_cases hn2' : n = 2
    ·
      subst hn2'
      have hs : IsSimpleGroup K := hT.isSimple
      have h60 : Nat.card K = 60 := by rw [hT.card_eq]; norm_num
      exact (hne (Or.inl (CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five h60))).elim
    · exact k32_noDatum_bender_psl2 hX hT (by omega) hd
  · subst hi
    exact k32_noDatum_bender_nonabelian hX hB hq2 le_rfl (k32_out_cyclic_sylow hT) hd
  · subst hi
    exact k32_noDatum_bender_nonabelian hX hB hq2 (by norm_num) (k32_out_cyclic_sylow hT) hd

end CFSG.QuasithinUnique.DoubleA3
