module

public import CFSG.ClassicalInvolution.Sp62Rec.Pkg
import CFSG.ClassicalInvolution.Sp62Rec.Balance
import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G} {T : Sylow 2 G} {A X : Subgroup G}

theorem E8ZPkg.centralizer_eq_zpowers (P : E8ZPkg z e E B T A X)
    (hodd : oddCoreIn (Subgroup.centralizer ({e} : Set G)) = ⊥)
    (φ : ↥B ≃* ↥Hhat) (hφE : (E.subgroupOf B).map φ.toMonoidHom = E0.subgroupOf Hhat)
    (he2 : e * e = 1) (he1 : e ≠ 1)
    (hCE0 : ∀ x ∈ Hhat, (∀ y ∈ E0, x * y = y * x) → x = 1 ∨ x = alpha) :
    Subgroup.centralizer (E : Set G) = Subgroup.zpowers e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Ce, hCe⟩ : ∃ C : Subgroup G, C = Subgroup.centralizer ({e} : Set G) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ C : Subgroup G, C = Subgroup.centralizer (E : Set G) := ⟨_, rfl⟩
  rw [← hCe] at hodd
  have hCemem : ∀ x, x ∈ Ce ↔ x * e = e * x := fun x => by
    rw [hCe]
    exact Subgroup.mem_centralizer_singleton_iff
  have hYmem : ∀ x, x ∈ Y ↔ ∀ h ∈ E, h * x = x * h := fun x => by
    rw [hY]
    exact Subgroup.mem_centralizer_iff
  have hEB : E ≤ B := P.E_le_B
  have hBC : B ≤ Ce := by
    rw [hCe]
    exact P.B_le
  have hEC : E ≤ Ce := hEB.trans hBC
  have heE : e ∈ E := P.e_mem
  have hTB : (T : Subgroup G) ≤ B := P.T_le
  have hEc : ∀ g ∈ Ce, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    intro g hg x hx
    have hgC : g ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [← hCe]
      exact hg
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rw [P.E_normal g hgC] at h1
    exact h1
  have hYCe : Y ≤ Ce := by
    intro g hg
    rw [hYmem] at hg
    exact (hCemem g).mpr (hg e heE).symm
  have hY_e : e ∈ Y := by
    rw [hYmem]
    intro h hh
    exact (hCemem h).mp (hEC hh)
  have hYconj : ∀ g ∈ Ce, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    rw [hYmem]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ E := by
      have := hEc g⁻¹ (Ce.inv_mem hg) x hx
      rwa [inv_inv] at this
    have hxy : (g⁻¹ * x * g) * y = y * (g⁻¹ * x * g) := (hYmem y).mp hy _ hx'
    calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxy]
      _ = g * y * g⁻¹ * x := by group
  have hCeN : Ce ≤ Subgroup.normalizer (Y : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hYconj g hg y
    · intro hy
      have := hYconj g⁻¹ (Ce.inv_mem hg) _ hy
      simpa [mul_assoc] using this
  have hoddY : oddCoreIn Y = ⊥ := by
    have hsub : IsSubnormal Y Ce :=
      isSubnormal_of_normal_subgroupOf hYCe
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hYCe).mpr hCeN)
    have h1 := oddCoreIn_le_of_isSubnormal hsub
    rw [hodd] at h1
    exact le_bot_iff.mp h1
  have hE0H : E0 ≤ Hhat := by
    show ⁅Hhat, Hhat⁆ ≤ Hhat
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hTY : Nat.card ↥((T : Subgroup G) ⊓ Y) ≤ 2 := by
    have hS : Nat.card ↥({1, ⟨alpha, alpha_mem_Hhat⟩} : Set ↥Hhat) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      calc ({1, ⟨alpha, alpha_mem_Hhat⟩} : Set ↥Hhat).ncard
          ≤ ({⟨alpha, alpha_mem_Hhat⟩} : Set ↥Hhat).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have hcommute : ∀ (t : G) (ht : t ∈ (T : Subgroup G)), t ∈ Y →
        ∀ y ∈ E0, (φ ⟨t, hTB ht⟩).1 * y = y * (φ ⟨t, hTB ht⟩).1 := by
      intro t ht htY y hy
      have hyH : y ∈ Hhat := hE0H hy
      have hmem : (⟨y, hyH⟩ : ↥Hhat) ∈ E0.subgroupOf Hhat := Subgroup.mem_subgroupOf.mpr hy
      rw [← hφE] at hmem
      obtain ⟨b, hb, hbφ⟩ := Subgroup.mem_map.mp hmem
      have hbE : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
      have hbt : (b : G) * t = t * (b : G) := (hYmem t).mp htY (b : G) hbE
      have hbt' : b * ⟨t, hTB ht⟩ = ⟨t, hTB ht⟩ * b := Subtype.ext hbt
      have h2 := congrArg φ hbt'
      rw [map_mul, map_mul] at h2
      have h3 : φ b = ⟨y, hyH⟩ := hbφ
      rw [h3] at h2
      exact (congrArg Subtype.val h2).symm
    have hmemS : ∀ (t : G) (ht : t ∈ (T : Subgroup G)), t ∈ Y →
        φ ⟨t, hTB ht⟩ ∈ ({1, ⟨alpha, alpha_mem_Hhat⟩} : Set ↥Hhat) := by
      intro t ht htY
      rcases hCE0 _ (φ ⟨t, hTB ht⟩).2 (fun y hy => hcommute t ht htY y hy) with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext h))
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext h)))
    have hinj : Function.Injective (fun t : ↥((T : Subgroup G) ⊓ Y) =>
        (⟨φ ⟨t.1, hTB (Subgroup.mem_inf.mp t.2).1⟩,
          hmemS t.1 (Subgroup.mem_inf.mp t.2).1 (Subgroup.mem_inf.mp t.2).2⟩ :
            ↥({1, ⟨alpha, alpha_mem_Hhat⟩} : Set ↥Hhat))) := by
      intro t₁ t₂ h
      have h1 : φ ⟨t₁.1, hTB (Subgroup.mem_inf.mp t₁.2).1⟩ =
          φ ⟨t₂.1, hTB (Subgroup.mem_inf.mp t₂.2).1⟩ := congrArg Subtype.val h
      have h2 := φ.injective h1
      exact Subtype.ext (Subtype.mk.inj h2)
    exact (Nat.card_le_card_of_injective _ hinj).trans hS
  have hQ2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Y → Nat.card ↥Q ≤ 2 := by
    intro Q hQ hQY
    have hQCe : Q ≤ Ce := hQY.trans hYCe
    have hQc : IsPGroup 2 (Q.subgroupOf Ce) :=
      IsPGroup.comap_of_ker_isPGroup hQ Ce.subtype
        (IsPGroup.ker_isPGroup_of_injective Ce.subtype_injective)
    obtain ⟨S₁, hS₁⟩ := IsPGroup.exists_le_sylow hQc
    have hTCe : (T : Subgroup G) ≤ Ce := hTB.trans hBC
    obtain ⟨Tc, hTc⟩ : ∃ Tc : Sylow 2 ↥Ce,
        (Tc : Subgroup ↥Ce) = (T : Subgroup G).subgroupOf Ce :=
      ⟨T.subtype hTCe, rfl⟩
    haveI : Finite (Sylow 2 ↥Ce) :=
      Finite.of_injective (fun P : Sylow 2 ↥Ce => (P : Set ↥Ce)) SetLike.coe_injective
    obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥Ce) Tc S₁
    have hconj : ∀ q ∈ Q, (m : G)⁻¹ * q * (m : G) ∈ (T : Subgroup G) := by
      intro q hq
      have hqS : (⟨q, hQCe hq⟩ : ↥Ce) ∈ S₁ := hS₁ (Subgroup.mem_subgroupOf.mpr hq)
      have hqS' : (⟨q, hQCe hq⟩ : ↥Ce) ∈ MulAut.conj m • (Tc : Subgroup ↥Ce) := by
        rw [← Sylow.coe_subgroup_smul, hm]
        exact hqS
      obtain ⟨s, hsT, hs⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hqS'
      have hsT' : (s : G) ∈ (T : Subgroup G) := by
        rw [hTc] at hsT
        exact Subgroup.mem_subgroupOf.mp hsT
      have hq' : (m : G) * (s : G) * (m : G)⁻¹ = q := congrArg Subtype.val hs
      have hs' : (m : G)⁻¹ * q * (m : G) = s := by
        rw [← hq']
        group
      rw [hs']
      exact hsT'
    have hYm : ∀ q ∈ Q, (m : G)⁻¹ * q * (m : G) ∈ Y := by
      intro q hq
      have := hYconj (m : G)⁻¹ (Ce.inv_mem m.2) q (hQY hq)
      rwa [inv_inv] at this
    have hinj : Function.Injective (fun q : ↥Q =>
        (⟨(m : G)⁻¹ * q.1 * (m : G), Subgroup.mem_inf.mpr ⟨hconj q.1 q.2, hYm q.1 q.2⟩⟩ :
          ↥((T : Subgroup G) ⊓ Y))) := by
      intro q₁ q₂ h
      have h' : (m : G)⁻¹ * q₁.1 * (m : G) = (m : G)⁻¹ * q₂.1 * (m : G) :=
        congrArg Subtype.val h
      apply Subtype.ext
      calc q₁.1 = (m : G) * ((m : G)⁻¹ * q₁.1 * (m : G)) * (m : G)⁻¹ := by group
        _ = (m : G) * ((m : G)⁻¹ * q₂.1 * (m : G)) * (m : G)⁻¹ := by rw [h']
        _ = q₂.1 := by group
    exact (Nat.card_le_card_of_injective _ hinj).trans hTY
  have hYcard : Nat.card ↥Y ≤ 2 := by
    obtain ⟨S⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
    have hSle : Nat.card S ≤ 2 := by
      have hQ2' : IsPGroup 2 ((S : Subgroup ↥Y).map Y.subtype) :=
        S.isPGroup'.map Y.subtype
      have hle := hQ2 _ hQ2' (Subgroup.map_subtype_le _)
      rwa [Subgroup.card_map_of_injective Y.subtype_injective] at hle
    have hcyc : IsCyclic S := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
      rcases n with _ | _ | n
      · have h1 : Nat.card S = 1 := by simpa using hn
        haveI : Subsingleton S := (Nat.card_eq_one_iff_unique.mp h1).1
        exact isCyclic_of_subsingleton
      · have h2 : Nat.card S = 2 := by simpa using hn
        exact isCyclic_of_prime_card (p := 2) h2
      · exfalso
        have h4 : 4 ≤ Nat.card S := by
          rw [hn, pow_succ, pow_succ]
          have := pow_pos (by norm_num : (0 : ℕ) < 2) n
          omega
        omega
    have hcomp := CFSG.cyclic_sylow_normal_odd_complement S hcyc
    have hidx := hcomp.2.2.2.1.2.2.1
    have hpp : CFSG.pPrimeCore 2 ↥Y = ⊥ := (oddCoreIn_eq_bot_iff Y).mp hoddY
    rw [hpp, Subgroup.index_bot] at hidx
    rw [hidx]
    exact hSle
  have hzp : Nat.card ↥(Subgroup.zpowers e) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [sq]; exact he2) he1]
  have hle : Subgroup.zpowers e ≤ Y := Subgroup.zpowers_le.mpr hY_e
  rw [← hY]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hzp]; exact hYcard)).symm

end CFSG.ClassicalInvolution.Sp62Rec
