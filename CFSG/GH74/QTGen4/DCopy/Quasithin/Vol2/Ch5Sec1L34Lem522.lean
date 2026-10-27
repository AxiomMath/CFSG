module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem522
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs522
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Thm4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem522S331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise commutatorElement

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem quasithinV2_K_eq_bot_F4 (h5114 : Stmt5_1_14_first_F4) : quasithinV2 (oTwoUpper H) = ⊥ := by
  obtain ⟨⟨hmax, -, hnf⟩, -⟩ := h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34
  by_contra hne
  apply hnf
  refine ⟨hmax.1, ?_, ?_, hne⟩
  · intro N hNK _ hN2
    refine le_antisymm hNK ((Subgroup.closure_le _).mpr ?_)
    rintro y ⟨hyH, hyo⟩
    obtain ⟨k, hk⟩ := hN2 y (mem_oTwoUpper_of_odd hyH hyo)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hyo) : Nat.Coprime (2 ^ k) (orderOf y))
    rw [← hm]
    exact N.pow_mem hk m
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (quasithinGenFitting_eq_pCoreOf_iff _ 2).mpr h.charTwo_K

theorem conj_eq_of_mem_centerOf_F4 (h5114 : Stmt5_1_14_first_F4) {x : G} (hx : x ∈ oTwoUpper H)
    (hodd : Odd (orderOf x)) {a : G}
    (ha : a ∈ pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (pCoreOf 2 (oTwoUpper H) : Set G)) :
    x * a * x⁻¹ = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  have hV := h.quasithinV2_K_eq_bot_F4 h5114
  have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 K hx
  have hxA : x ∈ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) :
      Set G) :=
    le_normalizer_inf (X := Subgroup.zpowers x)
      (Subgroup.zpowers_le.mpr hxQ)
      (Subgroup.zpowers_le.mpr (le_normalizer_centralizer_of_le_normalizer
        (Subgroup.zpowers_le.mpr hxQ) (Subgroup.mem_zpowers x))) (Subgroup.mem_zpowers x)
  refine conj_eq_of_odd_of_sq ((pCoreOf_isPGroup 2 K).to_le inf_le_left)
    (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp hb.2 a ha.1)) hxA hodd ?_ a ha
  intro b hb hb2
  have hmem : ⁅b, x⁆ ∈ quasithinV2 K :=
    Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨hb, hb2⟩) hx
  rw [hV, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  rw [← hmem, mul_assoc, mul_inv_cancel, mul_one]

end Hyp5_1_14

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem commutator_eq_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    ⁅conjClosure Z₁ D₃, pCoreOf 2 (oTwoUpper H)⁆ = Z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  set V₂ := conjClosure Z₁ D₃ with hV₂def
  have hHC := s.H_le_centralizer_F4 h5114
  have h21 := (h521 G T M L V H B D D₃ Z₁ H n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34
    hnot s.le_D s.card_D₃ s.z1 le_rfl hHC).1
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hQH : Q ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hle : ⁅V₂, Q⁆ ≤ Z₁ := (Subgroup.commutator_mono (le_conjClosure V₂ H) hQH).trans h21
  have hne : ⁅V₂, Q⁆ ≠ ⊥ := by
    intro hb
    have hVQ : V₂ ≤ Subgroup.centralizer (Q : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
    have hV₂H : V₂ ≤ H := s.V₂_le_T.trans s.hyp.hyp.hStar.1.1

    have hodd : ∀ x ∈ H, Odd (orderOf x) →
        x ∈ Subgroup.centralizer (V₂ : Set G) := by
      intro x hxH hxo
      have hxK : x ∈ K := mem_oTwoUpper_of_odd hxH hxo
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      set c := x * v * x⁻¹ * v⁻¹ with hcdef
      have hvH := hV₂H hv
      have hcK : c ∈ K := by
        have h1 : v * x⁻¹ * v⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hHK hvH) x⁻¹).mp (K.inv_mem hxK)
        have e : c = x * (v * x⁻¹ * v⁻¹) := by rw [hcdef]; group
        rw [e]; exact K.mul_mem hxK h1
      have hcC : c ∈ Subgroup.centralizer (Q : Set G) := by
        have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 K hxK
        have h1 : x * v * x⁻¹ ∈ Subgroup.centralizer (Q : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_centralizer_of_le_normalizer
            (Subgroup.zpowers_le.mpr hxQ) (Subgroup.mem_zpowers x)) v).mp (hVQ hv)
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hVQ hv))
      have hcQ : c ∈ Q := s.hyp.charTwo_K ⟨hcK, hcC⟩
      have hxc : x * c * x⁻¹ = c := s.hyp.conj_eq_of_mem_centerOf_F4 h5114 hxK hxo ⟨hcQ, hcC⟩
      have hxv : x * v * x⁻¹ = c * v := by rw [hcdef]; group
      have hiter : ∀ j : ℕ, x ^ j * v * (x ^ j)⁻¹ = c ^ j * v := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          have hxcj : x * c ^ j * x⁻¹ = c ^ j := by rw [← conj_pow, hxc]
          calc x ^ (j + 1) * v * (x ^ (j + 1))⁻¹ = x * (x ^ j * v * (x ^ j)⁻¹) * x⁻¹ := by
                rw [pow_succ']; group
            _ = x * (c ^ j * v) * x⁻¹ := by rw [ihj]
            _ = (x * c ^ j * x⁻¹) * (x * v * x⁻¹) := by group
            _ = c ^ (j + 1) * v := by rw [hxcj, hxv, ← mul_assoc, ← pow_succ]
      have hm := hiter (orderOf x)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
      have hcm : c ^ orderOf x = 1 := by
        have := congrArg (· * v⁻¹) hm
        simpa using this.symm
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 K) ⟨c, hcQ⟩
      have hck : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hgcd : orderOf c ∣ Nat.gcd (2 ^ k) (orderOf x) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hck) (orderOf_dvd_of_pow_eq_one hcm)
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hxo)),
        Nat.dvd_one, orderOf_eq_one_iff] at hgcd
      have : x * v * x⁻¹ = v := by rw [hxv, hgcd, one_mul]
      have e : x * v = v * x := by
        have := congrArg (· * x) this
        simpa [mul_assoc] using this
      exact e.symm
    have hKC : K ≤ Subgroup.centralizer (V₂ : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxH, hxo⟩
      exact hodd x hxH hxo

    apply s.not_le
    have hHN : H ≤ Subgroup.normalizer (V₂ : Set G) := by
      rw [s.hyp.H_eq_sup]
      exact sup_le (hKC.trans (Subgroup.centralizer_le_normalizer _)) (s.T_le_normalizer_V₂ hF)
    obtain ⟨z, hz, hz1⟩ := s.exists_z
    have hV₂ne : V₂ ≠ ⊥ := fun hb' => hz1 (by
      have := (le_conjClosure Z₁ D₃) hz
      rw [← hV₂def, hb'] at this
      exact Subgroup.mem_bot.mp this)
    have hloc : IsTwoLocal (Subgroup.normalizer (V₂ : Set G)) :=
      ⟨V₂, hV₂ne, isPGroup_of_isElemAbelian s.isElemAbelian_V₂, rfl⟩
    obtain ⟨M', hM', hle'⟩ := exists_maxTwoLocal_ge hloc
    have hM'eq := (s.hyp.isUniqueM_F4 h5114).2 M' ⟨hM', hHN.trans hle'⟩
    exact (le_normalizer_conjClosure Z₁ D₃).trans (hM'eq ▸ hle')

  have hd : Nat.card ↥(⁅V₂, Q⁆) ∣ 2 := s.card_Z₁ ▸ Subgroup.card_dvd_of_le hle
  have h1 : Nat.card ↥(⁅V₂, Q⁆) ≠ 1 := fun h1 => hne (Subgroup.card_eq_one.mp h1)
  have h2 : Nat.card ↥(⁅V₂, Q⁆) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd h h1
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h2, s.card_Z₁])

section Swap

variable {z d : G} (hz : z ∈ Z₁) (hz1 : z ≠ 1) (hd : d ∈ D₃) (hd1 : d ≠ 1)
include hz hz1 hd hd1

theorem mem_centralizer_of_conj_eq_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) {x : G}
    (hxz : x * z * x⁻¹ = z) (hxb : x * (d * z * d⁻¹) * x⁻¹ = d * z * d⁻¹) :
    x ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hxw : x * w * x⁻¹ = w := by
    obtain ⟨u, hu, rfl | rfl⟩ := s.mem_V₂_iff_F4 hz hz1 hd hd1 h5114 hF hw
    · rcases s.eq_one_or_eq hz hz1 hu with hu1 | hu1
      · rw [hu1]; group
      · rw [hu1]; exact hxz
    · rcases s.eq_one_or_eq hz hz1 hu with hu1 | hu1
      · rw [hu1, one_mul]; exact hxb
      · rw [hu1, show x * (z * (d * z * d⁻¹)) * x⁻¹ =
          (x * z * x⁻¹) * (x * (d * z * d⁻¹) * x⁻¹) by group, hxz, hxb]
  calc w * x = x * w * x⁻¹ * x := by rw [hxw]
    _ = x * w := by group

theorem conj_eq_mul_of_not_mem_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) {x : G}
    (hxN : x ∈ Subgroup.normalizer (conjClosure Z₁ D₃ : Set G)) (hxz : x * z * x⁻¹ = z)
    (hxC : x ∉ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) :
    x * (d * z * d⁻¹) * x⁻¹ = z * (d * z * d⁻¹) := by
  obtain ⟨-, -, hb1, hbz⟩ := s.b_props_F4 hz hz1 hd hd1 h5114
  have hb : x * (d * z * d⁻¹) * x⁻¹ ∈ conjClosure Z₁ D₃ :=
    (Subgroup.mem_normalizer_iff.mp hxN _).mp (mem_conjClosure hd hz)
  have hback : d * z * d⁻¹ = x⁻¹ * (x * (d * z * d⁻¹) * x⁻¹) * x := by group
  obtain ⟨u, hu, h | h⟩ := s.mem_V₂_iff_F4 hz hz1 hd hd1 h5114 hF hb
  · exfalso
    rcases s.eq_one_or_eq hz hz1 hu with hu1 | hu1
    · apply hb1
      rw [hback, h, hu1]; group
    · apply hbz
      rw [hback, h, hu1]
      exact inv_conj_eq_self hxz
  · rcases s.eq_one_or_eq hz hz1 hu with hu1 | hu1
    · exfalso
      refine hxC (s.mem_centralizer_of_conj_eq_F4 hz hz1 hd hd1 h5114 hF hxz ?_)
      rw [h, hu1, one_mul]
    · rw [h, hu1]

theorem mul_mem_centralizer_of_swap_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) {x : G}
    (hxz : x * z * x⁻¹ = z) (hxb : x * (d * z * d⁻¹) * x⁻¹ = z * (d * z * d⁻¹)) :
    d * x * d * x⁻¹ ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
  obtain ⟨hzb, hb2, -, -⟩ := s.b_props_F4 hz hz1 hd hd1 h5114
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp (s.Z₁_le_Z hz)).2.2
  have hc := s.c_eq_F4 hz hz1 hd hd1 h5114 hF
  have hxz' := inv_conj_eq_self hxz
  have hxb' := inv_conj_eq_of_conj_eq hz2 hxz hxb

  have hbzb : (d * z * d⁻¹) * (z * (d * z * d⁻¹)) = z := by
    calc (d * z * d⁻¹) * (z * (d * z * d⁻¹)) = (d * z * d⁻¹) * ((d * z * d⁻¹) * z) := by
          rw [hzb.eq]
      _ = ((d * z * d⁻¹) * (d * z * d⁻¹)) * z := by group
      _ = z := by
          have hbb : (d * z * d⁻¹) * (d * z * d⁻¹) = 1 := by rw [← sq]; exact hb2
          rw [hbb, one_mul]
  have hdzb : d * (z * (d * z * d⁻¹)) * d⁻¹ = z := by
    have e1 : d * (z * (d * z * d⁻¹)) * d⁻¹ = (d * z * d⁻¹) * (d ^ 2 * z * (d ^ 2)⁻¹) := by group
    rw [e1, hc]
    exact hbzb
  apply s.mem_centralizer_of_conj_eq_F4 hz hz1 hd hd1 h5114 hF
  · have e1 : d * x * d * x⁻¹ * z * (d * x * d * x⁻¹)⁻¹ =
        d * (x * (d * (x⁻¹ * z * x) * d⁻¹) * x⁻¹) * d⁻¹ := by group
    rw [e1, hxz', hxb, hdzb]
  · have e1 : d * x * d * x⁻¹ * (d * z * d⁻¹) * (d * x * d * x⁻¹)⁻¹ =
        d * (x * (d * (x⁻¹ * (d * z * d⁻¹) * x) * d⁻¹) * x⁻¹) * d⁻¹ := by group
    rw [e1, hxb', hdzb, hxz]

end Swap

theorem L₂_le_sup_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    conjClosure D₃ T ≤
      D₃ ⊔ (conjClosure D₃ T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) := by
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  have hD₃C : D₃ ≤ Subgroup.normalizer
      (Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) : Set G) :=
    le_normalizer_centralizer_of_le_normalizer (le_normalizer_conjClosure Z₁ D₃)
  refine conjClosure_le fun t ht e he => ?_
  have heL : e ∈ conjClosure D₃ T := le_conjClosure D₃ T he
  have hteL : t * e * t⁻¹ ∈ conjClosure D₃ T := mem_conjClosure ht he
  by_cases he1 : e = 1
  · rw [he1, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  have htz : t * z * t⁻¹ = z := s.conj_eq_of_mem_T ht hz
  by_cases htC : t ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)
  · have h1 : e⁻¹ * t * e ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp (hD₃C (D₃.inv_mem he)) t).mp htC
      simpa using this
    have h2 : e⁻¹ * (t * e * t⁻¹) ∈
        conjClosure D₃ T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ heL) hteL, ?_⟩
      have e1 : e⁻¹ * (t * e * t⁻¹) = (e⁻¹ * t * e) * t⁻¹ := by group
      rw [e1]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ htC)
    have e2 : t * e * t⁻¹ = e * (e⁻¹ * (t * e * t⁻¹)) := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right h2)
  · have htb := s.conj_eq_mul_of_not_mem_F4 hz hz1 he he1 h5114 hF (s.T_le_normalizer_V₂ hF ht)
      htz htC
    have h1 := s.mul_mem_centralizer_of_swap_F4 hz hz1 he he1 h5114 hF htz htb
    have h2 : e * t * e * t⁻¹ ∈
        conjClosure D₃ T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, h1⟩
      have e1 : e * t * e * t⁻¹ = e * (t * e * t⁻¹) := by group
      rw [e1]
      exact Subgroup.mul_mem _ heL hteL
    have e2 : t * e * t⁻¹ = e⁻¹ * (e * t * e * t⁻¹) := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (D₃.inv_mem he)) (Subgroup.mem_sup_right h2)

theorem normalizer_le_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    Subgroup.normalizer (conjClosure Z₁ D₃ : Set G) ≤ Subgroup.normalizer
      ((D₃ ⊔ pCoreOf 2 (Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) : Subgroup G) :
        Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  obtain ⟨d, hd, hd1⟩ := s.exists_d
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp (s.Z₁_le_Z hz)).2.2
  have hcomm := s.commutator_eq_F4 h5114 hF h521 hnot
  have hCz := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module
    s.hyp.l34).2.1.2 z (s.Z₁_le_Z hz) hz1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf s.hyp.hyp.hStar.1.1) (oTwoUpper_le H)
      (le_normalizer_oTwoUpper H)
  have hL₂S := s.L₂_le_sup_F4 h5114 hF
  have hS2 : IsPGroup 2 ↥(conjClosure D₃ T ⊓
      Subgroup.centralizer (conjClosure Z₁ D₃ : Set G)) :=
    hh.sylow.1.to_le ((inf_le_inf_right _ (le_sup_left : conjClosure D₃ T ≤
      conjClosure D₃ T ⊔ T)).trans (s.inf_centralizer_V₂_le_T_F4 h5114 hF))
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  set V₂ := conjClosure Z₁ D₃ with hV₂def
  set C := Subgroup.centralizer (V₂ : Set G) with hCdef
  set G₂ := Subgroup.normalizer (V₂ : Set G) with hG₂def
  set L₂ := conjClosure D₃ T with hL₂def
  set P := pCoreOf 2 C with hPdef
  set S := L₂ ⊓ C with hSdef

  have hCG : G₂ ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizer_of_le_normalizer le_rfl
  have hPG : G₂ ≤ Subgroup.normalizer (P : Set G) :=
    hCG.trans (normalizer_le_normalizer_pCoreOf 2 C)
  have hCG₂ : C ≤ G₂ := Subgroup.centralizer_le_normalizer _
  have hTG : T ≤ G₂ := s.T_le_normalizer_V₂ hF
  have hD₃G : D₃ ≤ G₂ := le_normalizer_conjClosure Z₁ D₃
  have hL₂G : L₂ ≤ G₂ := conjClosure_le fun t ht e he =>
    G₂.mul_mem (G₂.mul_mem (hTG ht) (hD₃G he)) (G₂.inv_mem (hTG ht))
  have hTL₂ : T ≤ Subgroup.normalizer (L₂ : Set G) := le_normalizer_conjClosure D₃ T

  have hQG : Q ≤ G₂ := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    rw [hcomm]
    exact le_conjClosure Z₁ D₃
  have hQT : Q ≤ T := (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK).trans inf_le_left
  have hCQ : C ≤ Subgroup.normalizer (Q : Set G) := by
    have h1 : C ≤ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (le_conjClosure Z₁ D₃ hz))
    exact h1.trans (hCz.trans (normalizer_le_normalizer_pCoreOf 2 K))
  have hCQP : ⁅C, Q⁆ ≤ P := by
    have h1 : ⁅C, Q⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_right.mp hCQ
    have h2 : ⁅C, Q⁆ ≤ C := Subgroup.le_normalizer_iff_commutator_le_left.mp (hQG.trans hCG)
    exact (le_inf h2 h1).trans (le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf Subgroup.le_normalizer hCQ)
      ((pCoreOf_isPGroup 2 K).to_le inf_le_right))

  have hL₂N : L₂ ≤ Subgroup.normalizer (P : Set G) := hL₂G.trans hPG
  have h3 : ⁅⁅L₂, Q⁆, C⁆ ≤ P := by
    refine commutator_commutator_le_of_rotate hL₂N (hQG.trans hPG) (hCG₂.trans hPG) ?_ ?_
    · rw [Subgroup.commutator_comm Q C]
      exact (Subgroup.commutator_mono hCQP le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hL₂N)
    · exact (Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hL₂G.trans hCG)) le_rfl).trans hCQP

  obtain ⟨q, hqQ, hqC⟩ : ∃ q ∈ Q, q ∉ C := by
    by_contra hcon
    have hQC : Q ≤ C := fun q hq => by_contra fun hqC => hcon ⟨q, hq, hqC⟩
    have hb : ⁅V₂, Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hQC)
    rw [hcomm] at hb
    have : z ∈ (⊥ : Subgroup G) := hb ▸ hz
    exact hz1 (Subgroup.mem_bot.mp this)
  have hqT : q ∈ T := hQT hqQ
  have hqz : q * z * q⁻¹ = z := s.conj_eq_of_mem_T hqT hz

  set Y := ⁅L₂, Q⁆ with hYdef
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) :=
    inf_le_left.trans (Subgroup.normalizer_commutator_ge_left L₂ Q)
  have hD₃Y : D₃ ≤ Y ⊔ S := by
    have hd'1 : d⁻¹ ≠ 1 := inv_ne_one.mpr hd1
    have hqb := s.conj_eq_mul_of_not_mem_F4 hz hz1 (D₃.inv_mem hd) hd'1 h5114 hF (hTG hqT) hqz hqC
    have hc := s.mul_mem_centralizer_of_swap_F4 hz hz1 (D₃.inv_mem hd) hd'1 h5114 hF hqz hqb
    have hdL : d ∈ L₂ := le_conjClosure D₃ T hd
    have hcS : d⁻¹ * q * d⁻¹ * q⁻¹ ∈ S := by
      refine Subgroup.mem_inf.mpr ⟨?_, hc⟩
      have e : d⁻¹ * q * d⁻¹ * q⁻¹ = d⁻¹ * (q * d⁻¹ * q⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hdL) (mem_conjClosure hqT (D₃.inv_mem hd))
    have hdq : ⁅d, q⁆ ∈ Y := Subgroup.commutator_mem_commutator hdL hqQ
    have hd2 : d ^ 2 ∈ Y ⊔ S := by
      have e : d ^ 2 = ⁅d, q⁆ * (d⁻¹ * q * d⁻¹ * q⁻¹)⁻¹ := by
        rw [sq, commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hdq)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right hcS))
    have hd21 : d ^ 2 ≠ 1 := by
      intro h1
      apply hd1
      have hd3 := pow_three_of_mem_of_card_three s.card_D₃ hd
      calc d = d ^ 3 * (d ^ 2)⁻¹ := by group
        _ = 1 := by rw [hd3, h1]; group
    rw [← zpowers_eq_of_card_prime Nat.prime_three s.card_D₃ (D₃.pow_mem hd 2) hd21]
    exact Subgroup.zpowers_le.mpr hd2
  have hL₂Y : L₂ ≤ Y := by
    have hL₂YS : L₂ ≤ Y ⊔ S := hL₂S.trans (sup_le hD₃Y le_sup_right)
    refine conjClosure_le fun t ht e he => ?_
    refine mem_of_odd_of_mem_sup hS2 hSY (hL₂YS (mem_conjClosure ht he)) ?_
    have h3' : (t * e * t⁻¹) ^ 3 = 1 := by
      rw [conj_pow, pow_three_of_mem_of_card_three s.card_D₃ he]
      group
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3')

  have hL₂C : ⁅L₂, C⁆ ≤ P := (Subgroup.commutator_mono hL₂Y le_rfl).trans h3
  have hPT : P ≤ T := by
    have h1 : P ≤ pCoreOf 2 G₂ := le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans hCG₂)
      hPG (pCoreOf_isPGroup 2 C)
    exact h1.trans (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf (hh.isSylowTwoOf hTG))
  have hCL₂ : C ≤ Subgroup.normalizer (L₂ : Set G) := by
    intro c hc
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    have hle : L₂ ≤ L₂.comap (MulAut.conj c).toMonoidHom := by
      refine conjClosure_le fun t ht e he => ?_
      show c * (t * e * t⁻¹) * c⁻¹ ∈ L₂
      have hx' : t * e * t⁻¹ ∈ L₂ := mem_conjClosure ht he
      have hcx : ⁅c, t * e * t⁻¹⁆ ∈ P := by
        apply hL₂C
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hc hx'
      have hmem : c * (t * e * t⁻¹) * c⁻¹ ∈ L₂ ⊔ P := by
        have e1 : c * (t * e * t⁻¹) * c⁻¹ = ⁅c, t * e * t⁻¹⁆ * (t * e * t⁻¹) := by
          rw [commutatorElement_def]; group
        rw [e1]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcx) (Subgroup.mem_sup_left hx')
      refine mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 C) (hPT.trans hTL₂) hmem ?_
      have h3' : (c * (t * e * t⁻¹) * c⁻¹) ^ 3 = 1 := by
        rw [conj_pow, conj_pow, pow_three_of_mem_of_card_three s.card_D₃ he]
        group
      exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3')
    exact hle hx

  have hSP : S ≤ P :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right (le_normalizer_inf hCL₂ Subgroup.le_normalizer) hS2
  have hL₂X : L₂ ≤ D₃ ⊔ P := hL₂S.trans (sup_le le_sup_left (hSP.trans le_sup_right))

  have hG₂ : G₂ ≤ (D₃ ⊔ C) ⊔ T := by
    intro g hg
    have hgz : g * z * g⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp hg z).mp (le_conjClosure Z₁ D₃ hz)
    have hgz1 : g * z * g⁻¹ ≠ 1 := by
      intro h1
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨e, he, hez⟩ := s.exists_conj_eq_F4 hz hz1 hd hd1 h5114 hF hgz hgz1
    have hyz : (e * g) * z * (e * g)⁻¹ = z := by
      rw [show (e * g) * z * (e * g)⁻¹ = e * (g * z * g⁻¹) * e⁻¹ by group, hez]
    have hyN : e * g ∈ G₂ := G₂.mul_mem (hD₃G he) hg
    by_cases hyC : e * g ∈ C
    · have e1 : g = e⁻¹ * (e * g) := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left (D₃.inv_mem he)))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hyC))
    · have hyb := s.conj_eq_mul_of_not_mem_F4 hz hz1 hd hd1 h5114 hF hyN hyz hyC
      have hqb := s.conj_eq_mul_of_not_mem_F4 hz hz1 hd hd1 h5114 hF (hTG hqT) hqz hqC
      have hqb' := inv_conj_eq_of_conj_eq hz2 hqz hqb
      have hw : (e * g) * q⁻¹ ∈ C := by
        apply s.mem_centralizer_of_conj_eq_F4 hz hz1 hd hd1 h5114 hF
        · rw [show e * g * q⁻¹ * z * (e * g * q⁻¹)⁻¹ = (e * g) * (q⁻¹ * z * q) * (e * g)⁻¹ by
            group, inv_conj_eq_self hqz, hyz]
        · rw [show e * g * q⁻¹ * (d * z * d⁻¹) * (e * g * q⁻¹)⁻¹ =
            (e * g) * (q⁻¹ * (d * z * d⁻¹) * q) * (e * g)⁻¹ by group, hqb',
            show (e * g) * (z * (d * z * d⁻¹)) * (e * g)⁻¹ =
              ((e * g) * z * (e * g)⁻¹) * ((e * g) * (d * z * d⁻¹) * (e * g)⁻¹) by group,
            hyz, hyb, ← mul_assoc, ← sq, hz2, one_mul]
      have e2 : g = e⁻¹ * ((e * g) * q⁻¹) * q := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left (D₃.inv_mem he)))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hw))) (Subgroup.mem_sup_right hqT)

  have hD₃X : D₃ ≤ Subgroup.normalizer ((D₃ ⊔ P : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hconj : ∀ y ∈ G₂, y ∈ Subgroup.normalizer (L₂ : Set G) →
      y ∈ Subgroup.normalizer ((D₃ ⊔ P : Subgroup G) : Set G) := by
    intro y hyG hyL
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    have hle : D₃ ⊔ P ≤ (D₃ ⊔ P).comap (MulAut.conj y).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro e he
        show y * e * y⁻¹ ∈ D₃ ⊔ P
        exact hL₂X ((Subgroup.mem_normalizer_iff.mp hyL e).mp (le_conjClosure D₃ T he))
      · intro p hp
        show y * p * y⁻¹ ∈ D₃ ⊔ P
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hPG hyG) p).mp hp)
    exact hle hx
  have hCX : C ≤ Subgroup.normalizer ((D₃ ⊔ P : Subgroup G) : Set G) :=
    fun c hc => hconj c (hCG₂ hc) (hCL₂ hc)
  have hTX : T ≤ Subgroup.normalizer ((D₃ ⊔ P : Subgroup G) : Set G) :=
    fun t ht => hconj t (hTG ht) (hTL₂ ht)
  exact hG₂.trans (sup_le (sup_le hD₃X hCX) hTX)

theorem two_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h519 : Stmt5_1_19_F4)
    (h522one : Stmt5_1_22_one_F4) (hKer : OrthKernelFact) (hBor : L34BorelFact)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    (n = 2 ∨ n = 4) ∧
      (IsNatModCh5 L ⁅V, L⁆ n ∨ IsSumOfTwo L ⁅V, L⁆ (fun W => IsNatModCh5 L W n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hred := s.hyp.module.isTwoReducedIn
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hVL : ⁅V, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have : l * v⁻¹ * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
    have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact V.mul_mem hv this
  rcases h519 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34 hnot D₃
      s.le_D s.card_D₃ with
    ⟨-, ⟨hn2, hsum⟩ | ⟨hn24, hnat⟩⟩ | ⟨hn48, horth, -⟩ | ⟨-, -, -, -, hD₃M', -⟩
  ·
    refine ⟨Or.inl hn2, Or.inr ?_⟩
    have heq : ⁅V, L⁆ = V := by
      refine le_antisymm hVL ?_
      obtain ⟨W₁, W₂, -, -, -, hsup, hN₁, hN₂⟩ := id hsum
      have hW₁ : W₁ ≤ V := (le_sup_left : W₁ ≤ W₁ ⊔ W₂).trans hsup.le
      have hW₂ : W₂ ≤ V := (le_sup_right : W₂ ≤ W₁ ⊔ W₂).trans hsup.le
      calc V = W₁ ⊔ W₂ := hsup.symm
        _ ≤ ⁅V, L⁆ := by
          refine sup_le ?_ ?_
          · rw [← hN₁.commutator_eq]
            exact Subgroup.commutator_mono hW₁ le_rfl
          · rw [← hN₂.commutator_eq]
            exact Subgroup.commutator_mono hW₂ le_rfl
    rw [heq]
    exact hsum
  · exact ⟨hn24, Or.inl hnat⟩
  ·
    exfalso
    obtain ⟨m, hnm, -⟩ := id horth
    have hm24 : m = 2 ∨ m = 4 := by omega
    have horth' : IsOrthCh5 L V (2 * m) := hnm ▸ horth

    have hZ1eq : Z₁ = quasithinOmegaOneCenter T := by
      rcases s.z1 with ⟨-, -, hZ | ⟨hsumZ, -⟩⟩
      · exact hZ
      · exfalso
        obtain ⟨W₁, -, hLW₁, -, -, -, hW₁, -⟩ := hsumZ
        have hW₁ne : ⁅W₁, L⁆ ≠ ⊥ := by
          rw [hW₁.commutator_eq]
          intro hb
          apply hW₁.not_le_centralizer
          rw [hb]
          intro l _
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Subgroup.mem_bot.mp hw, one_mul, mul_one]
        have h1 := hh.card_quot_dvd_card_autOn hLW₁ hW₁ne
        obtain ⟨-, Kf, _, _, π, -, hKf, hπ, -⟩ := hW₁.exists_equiv
        have h2 : Nat.card ↥(autOn L W₁) ≤ 60 := by
          rw [← OrthFour.card_statedSL_two (K := Kf) (by rw [hKf]; norm_num)]
          exact Nat.card_le_card_of_surjective π hπ
        have h3 := (Nat.le_of_dvd Nat.card_pos h1).trans h2
        rw [card_of_lieModel_L2 (by omega) hh.lie] at h3
        have h4 : 2 ^ 4 * (4 ^ 4 - 1) ≤ 2 ^ n * (4 ^ n - 1) := by
          apply Nat.mul_le_mul
          · exact Nat.pow_le_pow_right (by norm_num) (by omega)
          · exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1
        omega

    have hT2 : IsPGroup 2 T := hh.sylow.1
    have hVT : V ≤ T := hh.V_le_T s.hyp.module
    have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hred.2.1
    have hVne : V ≠ ⊥ := by
      intro hb
      apply s.hyp.module.2.2
      rw [hb, eq_bot_iff, Subgroup.commutator_le]
      intro v hv l _
      rw [Subgroup.mem_bot] at hv ⊢
      rw [hv]
      simp
    obtain ⟨z₀, hz₀V, hz₀1, hz₀Z⟩ :=
      exists_mem_omegaOneCenter hT2 hred.2.2.1 le_rfl hVT hTV hVne
    have hZV : Z₁ ≤ V := by
      rw [← zpowers_eq_of_card_prime Nat.prime_two s.card_Z₁ (hZ1eq ▸ hz₀Z) hz₀1]
      exact Subgroup.zpowers_le.mpr hz₀V

    obtain ⟨hDcyc, hDcard⟩ := hh.isCyclic_card_of_isHall hF s.hyp.notation59.2.1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥D)
    have hgord : orderOf g = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hg
    have hdvd : 2 ^ m + 1 ∣ orderOf g := by
      rw [hgord, hDcard, hnm, pow_mul']
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have h2 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      have e : (2 ^ m) ^ 2 - 1 = (2 ^ m + 1) * (2 ^ m - 1) := by
        zify [h1, h2]; ring
      rw [e]
      exact Dvd.intro _ rfl
    have hg0 : orderOf g ≠ 0 := by rw [hgord]; exact Nat.card_pos.ne'
    set x : ↥D := g ^ (orderOf g / (2 ^ m + 1)) with hxdef
    have hxord : orderOf x = 2 ^ m + 1 := orderOf_pow_orderOf_div hg0 hdvd
    have hxord' : orderOf (x : G) = 2 ^ m + 1 := by rw [Subgroup.orderOf_coe, hxord]
    have hprime : (2 ^ m + 1).Prime := by rcases hm24 with rfl | rfl <;> norm_num

    have hS : IsSylowTwoOf (T ⊓ L) L :=
      A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
    have hDm : Subgroup.zpowers (x : G) ≤ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (s.hyp.notation59.2.1.1 x.2)
    have hKer' := hKer G L V (T ⊓ L) (Subgroup.zpowers (x : G)) m horth' hS hDm
      (by rw [Nat.card_zpowers, hxord'])
    have hZ1x : ∀ y ∈ Z₁, (x : G) * y = y * x := by
      intro y hy
      have hyC : y ∈ V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
        ⟨hZV hy, Subgroup.centralizer_le (fun t ht => ht.1)
          (quasithinOmegaOneCenter_le_inf T (s.Z₁_le_Z hy)).2⟩
      exact Subgroup.mem_centralizer_iff.mp (hKer' hyC) x (Subgroup.mem_zpowers _)
    have hD₃x : ∀ e ∈ D₃, (x : G) * e = e * x := by
      intro e he
      have := hDcyc
      have hc := (IsCyclic.commGroup (α := ↥D)).mul_comm x ⟨e, s.le_D he⟩
      exact congrArg Subtype.val hc
    have hxC : (x : G) ∈ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hle : conjClosure Z₁ D₃ ≤
          Subgroup.centralizer ((Subgroup.zpowers (x : G) : Subgroup G) : Set G) := by
        refine conjClosure_le fun e he y hy => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        have hxe : Commute (x : G) e := hD₃x e he
        have hxy : Commute (x : G) y := hZ1x y hy
        exact ((hxe.mul_right hxy).mul_right hxe.inv_right).zpow_left k |>.eq
      exact (Subgroup.mem_centralizer_iff.mp (hle hv) x (Subgroup.mem_zpowers _)).symm

    set C := Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) with hCdef
    obtain ⟨hprod, -⟩ := h522one G T M L V H B D D₃ Z₁ n s.hyp.hyp s.hyp.notation59
      s.hyp.module s.hyp.l34 hnot s.le_D s.card_D₃ s.z1
    have hBC : B ≤ C := by
      intro b hb
      have : b ∈ ((T ⊓ C : Subgroup G) : Set G) * (B : Set G) :=
        Set.mem_mul.mpr ⟨1, (T ⊓ C).one_mem, b, hb, one_mul b⟩
      rw [hprod] at this
      exact this
    have hB3 := s.hyp.card_B_dvd_three_F4 h510 hBor

    have hsurj : Function.Surjective (fun b : ↥B =>
        (QuotientGroup.mk (⟨(b : G)⁻¹, C.inv_mem (hBC b.2)⟩ : ↥C) :
          ↥C ⧸ (T ⊓ C).subgroupOf C)) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H c =>
        have hc' : (c : G)⁻¹ ∈ ((T ⊓ C : Subgroup G) : Set G) * (B : Set G) := by
          rw [hprod]; exact C.inv_mem c.2
        obtain ⟨t, ht, b, hb, htb⟩ := Set.mem_mul.mp hc'
        refine ⟨⟨b, hb⟩, ?_⟩
        show (QuotientGroup.mk _ : ↥C ⧸ (T ⊓ C).subgroupOf C) = QuotientGroup.mk c
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have e : ((⟨(b : G)⁻¹, C.inv_mem (hBC hb)⟩ : ↥C)⁻¹ * c : ↥C) = (t : G)⁻¹ := by
          have : (c : G) = (t * b)⁻¹ := by rw [htb, inv_inv]
          simp [this]
        rw [e]
        exact (T ⊓ C).inv_mem ht
    have hidx : (T ⊓ C).relIndex C ≤ Nat.card B := by
      rw [Subgroup.relIndex, Subgroup.index]
      exact Nat.card_le_card_of_surjective _ hsurj

    have hpC : 2 ^ m + 1 ∣ Nat.card C := by
      have := orderOf_dvd_natCard (⟨(x : G), hxC⟩ : ↥C)
      rwa [Subgroup.orderOf_mk, hxord'] at this
    have hcardC := Subgroup.relIndex_mul_card (T ⊓ C) C
    rw [inf_of_le_left (inf_le_right : T ⊓ C ≤ C)] at hcardC
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hT2.to_le (inf_le_left : T ⊓ C ≤ T))
    rw [hk] at hcardC
    have hpi : 2 ^ m + 1 ∣ (T ⊓ C).relIndex C := by
      rw [← hcardC] at hpC
      have hcop : Nat.Coprime (2 ^ m + 1) (2 ^ k) :=
        Nat.Coprime.pow_right k ((Nat.coprime_primes hprime Nat.prime_two).mpr
          (by rcases hm24 with rfl | rfl <;> norm_num))
      exact hcop.dvd_of_dvd_mul_right hpC
    have hpos : 0 < (T ⊓ C).relIndex C := relIndex_pos' _ _
    have h1 := Nat.le_of_dvd hpos hpi
    have h2 := Nat.le_of_dvd (by norm_num) hB3
    have h3 : 5 ≤ 2 ^ m + 1 := by rcases hm24 with rfl | rfl <;> norm_num
    omega
  · exact absurd hD₃M' s.not_le

end Setup521

theorem stmt5_1_22_of_inputs_F4 (h5114 : Stmt5_1_14_first_F4) (h510 : Stmt5_1_10_F4) (h519 : Stmt5_1_19_F4)
    (h520 : Stmt5_1_20_F4) (h521 : Stmt5_1_21_F4) (h522one : Stmt5_1_22_one_F4) (hF : L2TorusFact)
    (hKer : OrthKernelFact) (hBor : L34BorelFact) : Stmt5_1_22_F4 := by
  intro G _ _ T M L V H B D D₃ Z₁ n hyp not59 hmod hl34 hnot hD₃ h3 hz1
  have s : Setup521 G T M L V H B D D₃ Z₁ n :=
    ⟨⟨hyp, not59, hmod, hl34⟩, hD₃, h3,
      (h520 G T M L V H B D n hyp not59 hmod hl34 hnot D₃ hD₃ h3).1, hz1⟩
  obtain ⟨hprod, hM⟩ := h522one G T M L V H B D D₃ Z₁ n hyp not59 hmod hl34 hnot hD₃ h3 hz1
  refine ⟨⟨?_, hM⟩, s.two_F4 hF h510 h519 h522one hKer hBor hnot,
    s.commutator_eq_F4 h5114 hF h521 hnot, s.normalizer_le_F4 h5114 hF h521 hnot⟩
  have hBC : B ≤ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
    intro b hb
    have : b ∈ ((T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) : Subgroup G) : Set G) *
        (B : Set G) := Set.mem_mul.mpr ⟨1, Subgroup.one_mem _, b, hb, one_mul b⟩
    rw [hprod] at this
    exact this
  refine le_antisymm (fun c hc => ?_) (sup_le inf_le_right hBC)
  have hc' : c ∈ ((T ⊓ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) : Subgroup G) : Set G) *
      (B : Set G) := by
    rw [hprod]; exact hc
  obtain ⟨t, ht, b, hb, rfl⟩ := Set.mem_mul.mp hc'
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hb)

end Setting

end CFSG.Quasithin.H13
