module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMathieuCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBound
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace CFSG.QuasithinUnique.DoubleA3.K32Mathieu

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

theorem centralizer_card_of_reps_ord {n m : ℕ} (hm : 0 < m) (hn : n < 2 ^ 32)
    (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) {gens gensInv : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    (data : List (Equiv.Perm (Fin n) × Subgroup (Equiv.Perm (Fin n))))
    (hreps : ∀ d ∈ data, g₀⁻¹ * d.1 ∈ Q.originalSubgroup ∧ orderOf d.1 = m) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ m) (data.map fun d => toTable d.1) cap =
      true)
    (hK : ∀ d ∈ data, d.2 ≤ centralizerIn Q.originalSubgroup d.1 ∧
      (conjClosure n gens gensInv (toTable d.1) cap).1.size * Nat.card d.2 =
        Nat.card Q.originalSubgroup) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = m →
      ∃ d ∈ data, Nat.card (centralizerIn Q.originalSubgroup u) = Nat.card d.2 := by
  have hok' : repsOK n gens gensInv (cosetOrderTables Q g₀ m)
      ((data.map Prod.fst).map toTable) cap = true := by
    rw [List.map_map]
    exact hok
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ hm
    (data.map Prod.fst) (fun r hr => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
      exact hreps d hd) cap hok'
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hKle, hKcard⟩ := hK d hd
  have hcent := centralizerIn_eq_of_le Q.originalSubgroup d.1 hKle (hsize _ hr) hKcard
  refine ⟨d, hd, ?_⟩
  rw [centralizerIn_conj _ hc, hcent, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem card_le_four_of_centralizerIn {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {c : ℕ}
    (hodd : c % 2 = 1)
    (hcent : ∀ u ∈ H, orderOf u = 3 → Nat.card (centralizerIn H u) = 4 * c)
    (g : H) (hg : orderOf g = 3) (W : Subgroup H) (hW : IsPGroup 2 ↥W)
    (hC : W ≤ Subgroup.centralizer ({g} : Set H)) : Nat.card ↥W ≤ 4 := by
  have hle : W.map H.subtype ≤ centralizerIn H (g : Equiv.Perm (Fin n)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizerIn]
    refine ⟨x.2, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hC hx)
    exact congrArg Subtype.val this
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective H.subtype_injective,
    hcent g g.2 ((Subgroup.orderOf_coe g).trans hg)] at h1
  exact k32_card_le_four_of_dvd hW hodd h1

abbrev m23R3 : Equiv.Perm (Fin 23) := m23Rep3.getD 0 1

theorem m23Rep3_eq : m23Rep3 = [m23R3] := rfl

theorem m23_ord3_rep_data :
    m23R3 ∈ m23Certificate.originalSubgroup ∧ orderOf m23R3 = 3 ∧
      m23Cent3Q.originalSubgroup ≤ centralizerIn m23Certificate.originalSubgroup m23R3 ∧
      Nat.card m23Cent3Q.originalSubgroup = 180 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m23_ord3_cover
  obtain ⟨hc, ho, hcomm⟩ := m23_ord3_cent
  refine ⟨evalCodes_mem _ m23_gens_mem _, ?_, ?_, ?_⟩
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m23Rep3_eq]; simp))
  · rw [m23Cent3Q, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m23_gens_mem w) hcomm
  · rw [← m23Cent3Q.orderCertificate_eq_card hc, ho]

theorem m23_ord3_centralizer_card
    : ∀ u ∈ NativeSporadic.M23, orderOf u = 3 →
    Nat.card (centralizerIn NativeSporadic.M23 u) = 180 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_ord3_cover
  obtain ⟨hr1, hro1, hK1, hKc1⟩ := m23_ord3_rep_data
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23Rep3_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m23Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ : ∃ d ∈ [(m23R3, m23Cent3Q.originalSubgroup)],
      Nat.card (centralizerIn m23Certificate.originalSubgroup u) = Nat.card d.2 := by
    refine centralizer_card_of_reps_ord (by norm_num) hn m23Certificate hQ
      (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh) _ ?_ 60000 hok ?_ u
      (by simpa using hu) ho
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  rw [hcard, hKc1]

theorem k32ZBound_m23
    : K32ZBound NativeSporadic.M23 4 :=
  k32ZBound_of_centralizer m23_center_eq_bot'
    (fun ω hω => k32_inner_of_orderThree m23_center_eq_bot'
      (by have := m23_mulAut_card; omega) ω hω)
    (fun g hg W hW hC => card_le_four_of_centralizerIn (c := 45) (by norm_num)
      (fun u hu ho => by rw [m23_ord3_centralizer_card u hu ho]) g hg W hW hC)

abbrev m22R3 : Equiv.Perm (Fin 22) := m22Rep3.getD 0 1

theorem m22Rep3_eq : m22Rep3 = [m22R3] := rfl

theorem m22_ord3_rep_data :
    m22R3 ∈ m22Certificate.originalSubgroup ∧ orderOf m22R3 = 3 ∧
      m22Cent3Q.originalSubgroup ≤ centralizerIn m22Certificate.originalSubgroup m22R3 ∧
      Nat.card m22Cent3Q.originalSubgroup = 36 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m22_ord3_cover
  obtain ⟨hc, ho, hcomm⟩ := m22_ord3_cent
  refine ⟨evalCodes_mem _ m22_gens_mem _, ?_, ?_, ?_⟩
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m22Rep3_eq]; simp))
  · rw [m22Cent3Q, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m22_gens_mem w) hcomm
  · rw [← m22Cent3Q.orderCertificate_eq_card hc, ho]

theorem m22_ord3_centralizer_card
    : ∀ u ∈ NativeSporadic.M22, orderOf u = 3 →
    Nat.card (centralizerIn NativeSporadic.M22 u) = 36 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_ord3_cover
  obtain ⟨hr1, hro1, hK1, hKc1⟩ := m22_ord3_rep_data
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22Rep3_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ : ∃ d ∈ [(m22R3, m22Cent3Q.originalSubgroup)],
      Nat.card (centralizerIn m22Certificate.originalSubgroup u) = Nat.card d.2 := by
    refine centralizer_card_of_reps_ord (by norm_num) hn m22Certificate hQ
      (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh) _ ?_ 14000 hok ?_ u
      (by simpa using hu) ho
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  rw [hcard, hKc1]

theorem k32ZBound_m22
    : K32ZBound NativeSporadic.M22 4 :=
  k32ZBound_of_centralizer m22_center_eq_bot'
    (fun ω hω => k32_inner_of_orderThree m22_center_eq_bot' m22_mulAut_card ω hω)
    (fun g hg W hW hC => card_le_four_of_centralizerIn (c := 9) (by norm_num)
      (fun u hu ho => by rw [m22_ord3_centralizer_card u hu ho]) g hg W hW hC)

end CFSG.QuasithinUnique.DoubleA3.K32Mathieu

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.DoubleA3.K32Mathieu

theorem k32_factorization_two {n k i : ℕ} (h : n = 2 ^ k * i) (hi : i % 2 = 1) :
    n.factorization 2 = k := by
  have hi0 : i ≠ 0 := by omega
  rw [h, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hi0]
  simp [Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ i),
    Nat.Prime.factorization_pow Nat.prime_two]

theorem k32_center_eq_pCore {K N : Type} [Group K] [Group N] (hq : CFSG.IsQuasisimple K)
    (e : (K ⧸ CFSG.pCore 2 K) ≃* N) (hN : Subgroup.center N = ⊥) (hN1 : Nontrivial N) :
    Subgroup.center K = CFSG.pCore 2 K := by
  have hCO : Subgroup.center K ≤ CFSG.pCore 2 K := by
    intro c hc
    have hcen : ∀ y : K ⧸ CFSG.pCore 2 K,
        y * (c : K ⧸ CFSG.pCore 2 K) = (c : K ⧸ CFSG.pCore 2 K) * y := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H z =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subgroup.mem_center_iff.mp hc z)
    have h2 : e (c : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hcen y]
    rw [hN, Subgroup.mem_bot] at h2
    have h3 : (c : K ⧸ CFSG.pCore 2 K) = 1 := e.injective (by rw [h2, map_one])
    exact (QuotientGroup.eq_one_iff c).mp h3
  refine le_antisymm hCO ?_
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.1
  have hnorm : ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have := hsimple
  have := hnorm
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K)))) with h | h
  · intro x hx
    have : QuotientGroup.mk' (Subgroup.center K) x ∈
        (CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K)) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · exfalso
    have htop : CFSG.pCore 2 K = ⊤ := by
      rw [eq_top_iff]
      intro k _
      have : QuotientGroup.mk' (Subgroup.center K) k ∈
          (CFSG.pCore 2 K).map (QuotientGroup.mk' (Subgroup.center K)) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨x, hx, hxk⟩ := this
      have hkx : x⁻¹ * k ∈ Subgroup.center K := by
        rw [← QuotientGroup.eq]
        exact hxk
      have : k = x * (x⁻¹ * k) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx (hCO hkx)
    obtain ⟨a, b, hab⟩ := exists_pair_ne N
    have h1 : e.symm a = e.symm b := by
      have h2 : ∀ y : K ⧸ CFSG.pCore 2 K, y = 1 := by
        intro y
        induction y using QuotientGroup.induction_on with
        | H z => exact (QuotientGroup.eq_one_iff z).mpr (htop ▸ Subgroup.mem_top z)
      rw [h2 (e.symm a), h2 (e.symm b)]
    exact hab (e.symm.injective h1)

theorem k32ExclM23_proved
    : K32ExclM23 := by
  intro K _ _ hq he _
  obtain ⟨e⟩ := he
  have e : K ≃* NativeSporadic.M23 := e
  have hperf : Group.IsPerfect K := hq.1
  have hZK : Subgroup.center K = ⊥ := by
    have h1 : (Subgroup.center K).map (e : K →* NativeSporadic.M23) = ⊥ := by
      rw [Subgroup.map_center_eq e, m23_center_eq_bot']
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center K) e.injective).mp h1
  let e' : K ⧸ Subgroup.center K ≃* NativeSporadic.M23 :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans (QuotientGroup.quotientBot.trans e)
  refine k32_noDatum_of_quot hperf e' k32ZBound_m23 ?_
  rw [k32_factorization_two (k := 7) (i := 79695) (by rw [m23_card]; norm_num) (by norm_num)]
  norm_num

theorem k32ExclM22_proved
    : K32ExclM22 := by
  intro K _ _ hq he _
  obtain ⟨e⟩ := he
  have e : K ≃* NativeSporadic.M22 := e
  have hperf : Group.IsPerfect K := hq.1
  have hZK : Subgroup.center K = ⊥ := by
    have h1 : (Subgroup.center K).map (e : K →* NativeSporadic.M22) = ⊥ := by
      rw [Subgroup.map_center_eq e, m22_center_eq_bot']
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center K) e.injective).mp h1
  let e' : K ⧸ Subgroup.center K ≃* NativeSporadic.M22 :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans (QuotientGroup.quotientBot.trans e)
  refine k32_noDatum_of_quot hperf e' k32ZBound_m22 ?_
  rw [k32_factorization_two (k := 7) (i := 3465) (by rw [m22_card]; norm_num) (by norm_num)]
  norm_num

theorem k32ExclM22Cover_proved
    : K32ExclM22Cover := by
  intro K _ _ hq he _
  obtain ⟨e⟩ := he
  have e : (K ⧸ CFSG.pCore 2 K) ≃* NativeSporadic.M22 := e
  have hperf : Group.IsPerfect K := hq.1
  have hnt : Nontrivial NativeSporadic.M22 :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [m22_card]; norm_num)
  have hZ := k32_center_eq_pCore hq e m22_center_eq_bot' hnt
  let e' : K ⧸ Subgroup.center K ≃* NativeSporadic.M22 :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans e
  refine k32_noDatum_of_quot hperf e' k32ZBound_m22 ?_
  rw [k32_factorization_two (k := 7) (i := 3465) (by rw [m22_card]; norm_num) (by norm_num)]
  norm_num

end CFSG.QuasithinUnique.DoubleA3
