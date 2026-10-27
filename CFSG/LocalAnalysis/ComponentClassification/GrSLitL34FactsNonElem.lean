module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Four
public import Certificates.Certificate22213
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenter

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open scoped commutatorElement

theorem nonElemParts :
    ((17, 8, 2, 0, 0) : ℕ × ℕ × ℕ × ℕ × ℕ) ∈ commData2 ∧
      ((27, 8, 0, 2, 0) : ℕ × ℕ × ℕ × ℕ × ℕ) ∈ commData2 := by
  have h := Certificates.certificate22213
  simp only [nonElemOK, nonElemData, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, List.contains_iff_mem] at h
  exact h

theorem comm_17_8 :
    cv (tw 17) * cv (tw 8) * (cv (tw 17))⁻¹ * (cv (tw 8))⁻¹ = z₁ ^ 2 := by
  have h := comm2_spec nonElemParts.1
  simpa using h

theorem comm_27_8 :
    cv (tw 27) * cv (tw 8) * (cv (tw 27))⁻¹ * (cv (tw 8))⁻¹ = z₂ ^ 2 := by
  have h := comm2_spec nonElemParts.2
  simpa using h

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem IsQSetting.exists_sq_ne_one
    (h : IsQSetting q l)
    {e : E} (he : e ∈ q.ker) (he2 : e * e ≠ 1) : l z₁ * l z₁ ≠ 1 ∨ l z₂ * l z₂ ≠ 1 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨i, j, rfl⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 he
  obtain ⟨hc1, hc2, -, -⟩ := lam_z_facts h.ker_le h.ql
  have hcomm : Commute (l z₁ ^ i) (l z₂ ^ j) :=
    (mem_center_iff.mp (Subgroup.pow_mem _ hc1 _) _).symm
  apply he2
  rw [← pow_two, hcomm.mul_pow, ← pow_mul, ← pow_mul, mul_comm i 2, mul_comm j 2, pow_mul,
    pow_mul, pow_two, pow_two, hcon.1, hcon.2, one_pow, one_pow, one_mul]

theorem nonelementaryCenterCommutator :
    ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
      (∃ z ∈ P ⊓ zStarIn K, z * z ≠ 1) →
      ∃ a ∈ P, a * a = 1 ∧ a ∉ zStarIn K ∧ ∃ w ∈ P ⊓ zStarIn K, w ≠ 1 ∧ w * w = 1 ∧
        w ∈ ⁅P ⊓ centralizer ({a} : Set G), P ⊓ centralizer ({a} : Set G)⁆ := by
  intro G _ _ K P hK hL hP hz
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hK hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨hc1, hc2, h14, h24⟩ := lam_z_facts hQ.ker_le hQ.ql
  obtain ⟨k, hk64, hk4, c, hc, hcne, hc2', hck⟩ : ∃ k < 64,
      wordPerm (tg k) * wordPerm (tg k) = wordPerm (tg 4) ∧ ∃ c : Jhat K,
        l (cv (tw k)) * l (cv (tw 8)) * (l (cv (tw k)))⁻¹ * (l (cv (tw 8)))⁻¹ = c ∧
        c ≠ 1 ∧ c * c = 1 ∧ c ∈ q.ker := by
    obtain ⟨z, hzZ, hz2⟩ := hz
    have hzk : jq K ⟨z, hP.1 hzZ.1⟩ ∈ q.ker := by
      rw [hqker]; exact (mem_zStarIn_iff _).1 hzZ.2
    have hzk2 : jq K ⟨z, hP.1 hzZ.1⟩ * jq K ⟨z, hP.1 hzZ.1⟩ ≠ 1 := by
      intro h1
      apply hz2
      refine eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hzZ.1 hzZ.1) ?_
      show jq K (⟨z, hP.1 hzZ.1⟩ * ⟨z, hP.1 hzZ.1⟩) = 1
      rw [map_mul]
      exact h1
    have hk1 : l z₁ ∈ q.ker := hQ.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₁)
    have hk2 : l z₂ ∈ q.ker := hQ.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₂)
    rcases hQ.exists_sq_ne_one hzk hzk2 with h1 | h2
    · refine ⟨17, by norm_num, (cce_spec (d := (0, 17, 4)) (by decide)).2.2.2, l z₁ ^ 2, ?_,
        by rwa [pow_two], ?_, pow_mem hk1 2⟩
      · have h := congrArg l comm_17_8
        simp only [map_mul, map_inv, map_pow] at h
        exact h
      · rw [← pow_add, h14]
    · refine ⟨27, by norm_num, (cce_spec (d := (1, 27, 4)) (by decide)).2.2.2, l z₂ ^ 2, ?_,
        by rwa [pow_two], ?_, pow_mem hk2 2⟩
      · have h := congrArg l comm_27_8
        simp only [map_mul, map_inv, map_pow] at h
        exact h
      · rw [← pow_add, h24]
  have hd₄ : ((4, 1, 1, 1) : ℕ × ℕ × ℕ × ℕ) ∈ sqData := by decide
  set ea := ilift l (4, 1, 1, 1) with head
  have hqa : q ea = wordPerm (tg 4) := hQ.q_ilift (by norm_num)
  have ha2 : ea * ea = 1 := hQ.ilift_mul_self hd₄
  set ex := l (cv (tw k)) with hexd
  set ey := l (cv (tw 8)) with heyd
  have hqx : q ex = wordPerm (tg k) := hQ.q_lift hk64
  have hqy : q ey = wordPerm (tg 8) := hQ.q_lift (by norm_num)
  have hxa : ex * ea = ea * ex := by
    have hu : ea⁻¹ * (ex * ex) ∈ center (Jhat K) := by
      rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, hqx, hk4, hqa, inv_mul_cancel]
    have hu' : ex * (ea⁻¹ * (ex * ex))⁻¹ = (ea⁻¹ * (ex * ex))⁻¹ * ex :=
      mem_center_iff.mp (inv_mem hu) ex
    calc ex * ea = ex * (ex * ex * (ea⁻¹ * (ex * ex))⁻¹) := by group
      _ = ex * ex * (ex * (ea⁻¹ * (ex * ex))⁻¹) := by group
      _ = ex * ex * ((ea⁻¹ * (ex * ex))⁻¹ * ex) := by rw [hu']
      _ = ea * ex := by group
  have hya : ey * ea = ea * ey := hQ.comm_of_Z0 (by rw [hqy]; exact mem_Z0.2 ⟨8, by simp, rfl⟩)
    (by rw [hqa]; exact mem_Z0.2 ⟨4, by simp, rfl⟩)
  obtain ⟨a, haP, haK, ha⟩ := (hT ea).1 (by rw [hqa]; exact tg_mem_T0 4 (by norm_num))
  obtain ⟨x, hxP, hxK, hx⟩ := (hT ex).1 (by rw [hqx]; exact tg_mem_T0 k hk64)
  obtain ⟨y, hyP, hyK, hy⟩ := (hT ey).1 (by rw [hqy]; exact tg_mem_T0 8 (by norm_num))
  have hcommP : ∀ {u v : G} (hu : u ∈ P) (hv : v ∈ P),
      jq K ⟨u, hP.1 hu⟩ * jq K ⟨v, hP.1 hv⟩ = jq K ⟨v, hP.1 hv⟩ * jq K ⟨u, hP.1 hu⟩ →
        u * v = v * u := by
    intro u v hu hv h
    apply eq_of_jq_eq hP.1 hP2 (P.mul_mem hu hv) (P.mul_mem hv hu)
    show jq K (⟨u, hP.1 hu⟩ * ⟨v, hP.1 hv⟩) = jq K (⟨v, hP.1 hv⟩ * ⟨u, hP.1 hu⟩)
    rw [map_mul, map_mul]
    exact h
  have hxa' : x * a = a * x := hcommP hxP haP (by
    rw [show (⟨x, hP.1 hxP⟩ : K) = ⟨x, hxK⟩ from rfl, show (⟨a, hP.1 haP⟩ : K) = ⟨a, haK⟩ from
      rfl, hx, ha]
    exact hxa)
  have hya' : y * a = a * y := hcommP hyP haP (by
    rw [show (⟨y, hP.1 hyP⟩ : K) = ⟨y, hyK⟩ from rfl, show (⟨a, hP.1 haP⟩ : K) = ⟨a, haK⟩ from
      rfl, hy, ha]
    exact hya)
  have hwP : ⁅x, y⁆ ∈ P := P.mul_mem (P.mul_mem (P.mul_mem hxP hyP) (P.inv_mem hxP))
    (P.inv_mem hyP)
  have hwq : jq K ⟨⁅x, y⁆, hP.1 hwP⟩ = c := by
    have e1 : (⟨⁅x, y⁆, hP.1 hwP⟩ : K) =
        ⟨x, hxK⟩ * ⟨y, hyK⟩ * (⟨x, hxK⟩ : K)⁻¹ * (⟨y, hyK⟩ : K)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hx, hy]
    exact hc
  refine ⟨a, haP, ?_, fun haZ => ?_, ⁅x, y⁆, ⟨hwP, (mem_zStarIn_iff (hP.1 hwP)).2 ?_⟩,
    fun hw1 => hcne ?_, ?_, ?_⟩
  · refine eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem haP haP) ?_
    show jq K (⟨a, haK⟩ * ⟨a, haK⟩) = 1
    rw [map_mul, ha]
    exact ha2
  · have hc4 := (mem_zStarIn_iff haK).1 haZ
    rw [← hqker, MonoidHom.mem_ker, ha, hqa, ← wordPerm_tg_zero] at hc4
    exact absurd (tg_injective (by norm_num) (by norm_num) hc4) (by norm_num)
  · rw [hwq, ← hqker]
    exact hck
  · rw [← hwq, show (⟨⁅x, y⁆, hP.1 hwP⟩ : K) = 1 from Subtype.ext hw1, map_one]
  · refine eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hwP hwP) ?_
    show jq K (⟨⁅x, y⁆, hP.1 hwP⟩ * ⟨⁅x, y⁆, hP.1 hwP⟩) = 1
    rw [map_mul, hwq]
    exact hc2'
  · exact commutator_mem_commutator ⟨hxP, mem_centralizer_singleton_iff.2 hxa'⟩
      ⟨hyP, mem_centralizer_singleton_iff.2 hya'⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
