module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OuterData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeModelC
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv CFSG.ComponentClassification.GrSLit.L34Facts

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

theorem phi_K_mem_NL (k : ↥h.K) :
    phi hKa (wbarMk h.B ⟨(k : H), K_le_W h k.2⟩) ∈ NL hKa := by
  rw [mem_subgroupOf]
  refine ⟨((k : OddBar h.K) : LK h), ?_⟩
  show _ = rhoBar hKa (wbarMk h.B _)
  rw [rhoBar_mk, ← rhoL_of_mem_K hKa k]

@[expose] def piK : ↥h.K →* ↥(NL hKa) :=
  ((phi hKa).comp ((wbarMk h.B).comp (Subgroup.inclusion (K_le_W h)))).codRestrict (NL hKa)
    (phi_K_mem_NL hKa)

theorem piK_apply (k : ↥h.K) :
    ((piK hKa k : ↥(GAut hKa)) : ↥(GAut hKa)) = phi hKa (wbarMk h.B ⟨(k : H), K_le_W h k.2⟩) :=
  rfl

theorem coe_piK (k : ↥h.K) :
    (((piK hKa k : ↥(GAut hKa)) : MulAut (LK h))) = MulAut.conj ((k : OddBar h.K) : LK h) := by
  show rhoBar hKa (wbarMk h.B _) = _
  rw [rhoBar_mk, ← rhoL_of_mem_K hKa k]
  rfl

theorem piK_surjective : Function.Surjective (piK hKa) := by
  intro γ
  have hγ := γ.2
  rw [mem_subgroupOf] at hγ
  obtain ⟨l, hl⟩ := hγ
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective l
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  rw [coe_piK]
  exact hl

theorem piK_eq_one_iff (hZ : center (OddBar h.K) = ⊥) {k : ↥h.K} :
    piK hKa k = 1 ↔ k ∈ pPrimeCore 2 ↥h.K := by
  constructor
  · intro hk
    have h1 := congrArg (fun γ : ↥(NL hKa) => ((γ : ↥(GAut hKa)) : MulAut (LK h))) hk
    simp only [coe_piK, OneMemClass.coe_one] at h1
    have h2 : ((k : OddBar h.K) : LK h) = 1 :=
      OutInv.conj_injective (h1.trans (map_one MulAut.conj).symm)
    rw [QuotientGroup.eq_one_iff, hZ, mem_bot, QuotientGroup.eq_one_iff] at h2
    exact h2
  · intro hk
    have h1 : (k : OddBar h.K) = 1 := (QuotientGroup.eq_one_iff k).2 hk
    have h2 : ((k : OddBar h.K) : LK h) = 1 := by
      rw [h1]
      rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_piK, h2, map_one]
    rfl

theorem piK_mem_Jhat {k : ↥h.K} (hk : (k : H) ∈ GSLit.fixedLayer h.J h.B) :
    ((piK hKa k : ↥(NL hKa)) : ↥(GAut hKa)) ∈ Jhat hKa :=
  ⟨wbarMk h.B ⟨(k : H), K_le_W h k.2⟩, ⟨⟨(k : H), K_le_W h k.2⟩, mem_subgroupOf.mpr hk, rfl⟩, rfl⟩

theorem exists_piK_of_mem_Jhat {γ : ↥(NL hKa)} (hγ : (γ : ↥(GAut hKa)) ∈ Jhat hKa) :
    ∃ k : ↥h.K, (k : H) ∈ GSLit.fixedLayer h.J h.B ∧ piK hKa k = γ := by
  obtain ⟨_, ⟨w, hw, rfl⟩, hγw⟩ := hγ
  rw [SetLike.mem_coe, mem_subgroupOf] at hw
  refine ⟨⟨(w : H), fixedLayer_le_K h hKa hw⟩, hw, Subtype.ext ?_⟩
  rw [piK_apply]
  exact hγw

theorem map_pPrimeCore_eq_bot
    {G : Type*} [Group G] [Finite G]
    (f : G →* ↥hjJ) (hf : Function.Surjective f) : (pPrimeCore 2 G).map f = ⊥ := by
  have hN : ((pPrimeCore 2 G).map f).Normal :=
    Subgroup.Normal.map pPrimeCore_normal f hf
  have hodd : Odd (Nat.card ((pPrimeCore 2 G).map f)) := by
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 G)) := pPrimeCore_coprime_card
    have h1 := Subgroup.card_map_dvd (H := pPrimeCore 2 G) f
    rcases Nat.even_or_odd (Nat.card ((pPrimeCore 2 G).map f)) with he | ho
    · exact absurd (Nat.Coprime.coprime_dvd_right (dvd_trans (even_iff_two_dvd.1 he) h1) hcop)
        (by norm_num)
    · exact ho
  rcases LocalCores.quasisimple_normal_subgroups isQuasisimple_hjJ hN with htop | hle
  · exfalso
    rw [htop, Subgroup.card_top, card_hjJ] at hodd
    exact absurd hodd (by decide)
  · rw [eq_bot_iff]
    intro n hn
    rw [mem_bot]
    have hn2 := mul_self_of_mem_ker (ker_hjQ ▸ hle hn)
    have hn2' : n * n = 1 := Subtype.ext hn2
    have hord : orderOf n ∣ Nat.card ((pPrimeCore 2 G).map f) :=
      Subgroup.orderOf_dvd_natCard _ hn
    have hord2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hn2')
    rcases (Nat.dvd_prime Nat.prime_two).1 hord2 with h1 | h1
    · exact orderOf_eq_one_iff.1 h1
    · rw [h1] at hord
      exact absurd (Odd.of_dvd_nat hodd hord) (by decide)

theorem exists_psi
    (hZ : center (OddBar h.K) = ⊥) {ι : ↥(NL hKa) →* Equiv.Perm (Fin 8330)}
    (hιinj : Function.Injective ι) (hιsurj : ∀ p ∈ heP, ∃ γ, ι γ = p)
    (hιJ : ∀ γ : ↥(NL hKa), (γ : ↥(GAut hKa)) ∈ Jhat hKa ↔ ι γ ∈ hjJ) :
    ∃ Ψ : OddBar h.J ≃* ↥hjJ, ∀ (j : H) (hjB : j ∈ GSLit.fixedLayer h.J h.B) (hjJ : j ∈ h.J),
      (Ψ (jq h.J ⟨j, hjJ⟩) : Equiv.Perm (Fin 8330)) =
        ι (piK hKa ⟨j, fixedLayer_le_K h hKa hjB⟩) := by
  set JB := GSLit.fixedLayer h.J h.B with hJB
  set τ : ↥JB →* ↥hjJ :=
    (ι.comp ((piK hKa).comp (Subgroup.inclusion (fixedLayer_le_K h hKa)))).codRestrict hjJ
      (fun j => (hιJ _).1 (piK_mem_Jhat hKa j.2)) with hτ
  have hτapp : ∀ j : ↥JB, (τ j : Equiv.Perm (Fin 8330)) =
      ι (piK hKa ⟨(j : H), fixedLayer_le_K h hKa j.2⟩) := fun _ => rfl
  have hτsurj : Function.Surjective τ := by
    intro g
    obtain ⟨γ, hγ⟩ := hιsurj g (hjJ_le g.2).1
    have hγJ : (γ : ↥(GAut hKa)) ∈ Jhat hKa := (hιJ γ).2 (hγ ▸ g.2)
    obtain ⟨k, hkB, rfl⟩ := exists_piK_of_mem_Jhat hKa hγJ
    refine ⟨⟨(k : H), hkB⟩, Subtype.ext ?_⟩
    rw [hτapp]
    exact hγ
  have hker : τ.ker = pPrimeCore 2 ↥JB := by
    apply le_antisymm
    · intro j hj
      apply ker_jbToK_le h hKa
      rw [MonoidHom.mem_ker] at hj ⊢
      have h1 : ι (piK hKa ⟨(j : H), fixedLayer_le_K h hKa j.2⟩) = 1 := by
        rw [← hτapp, hj]
        rfl
      have h2 := hιinj (h1.trans (map_one ι).symm)
      rw [piK_eq_one_iff hKa hZ] at h2
      rw [jbToK_apply, QuotientGroup.eq_one_iff]
      exact h2
    · have := map_pPrimeCore_eq_bot τ hτsurj
      intro j hj
      rw [MonoidHom.mem_ker]
      have h1 : τ j ∈ (pPrimeCore 2 ↥JB).map τ := ⟨j, hj, rfl⟩
      rw [this, mem_bot] at h1
      exact h1
  obtain ⟨e₁, he₁⟩ := exists_oddBar_JB_equiv h
  set E : ↥JB ⧸ pPrimeCore 2 ↥JB ≃* ↥hjJ :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective τ hτsurj) with hE
  refine ⟨e₁.symm.trans E, fun j hjB hjJ' => ?_⟩
  have h1 : e₁.symm (jq h.J ⟨j, hjJ'⟩) = ((⟨j, hjB⟩ : ↥JB) : ↥JB ⧸ pPrimeCore 2 ↥JB) := by
    rw [MulEquiv.symm_apply_eq, he₁ ⟨j, hjB⟩ hjJ']
    rfl
  rw [MulEquiv.trans_apply, h1]
  exact hτapp ⟨j, hjB⟩

end CFSG.ComponentClassification.GSThmB.CF23L34
