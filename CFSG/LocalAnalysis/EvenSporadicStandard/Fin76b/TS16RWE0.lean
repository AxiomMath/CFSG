module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWPhiM
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWLab2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAdm

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Monster.B.Co2

section Moves

variable {M : Type*} [Group M]

theorem moves_lemma {a z σ g : M} (hza : z * a * z⁻¹ = a⁻¹) (hσa : σ * a * σ⁻¹ = a)
    (hgz : g * z * g⁻¹ = σ) (hne : a ≠ a⁻¹) : g * a * g⁻¹ ≠ a ∧ g * a * g⁻¹ ≠ a⁻¹ := by
  have key : σ * (g * a * g⁻¹) * σ⁻¹ = (g * a * g⁻¹)⁻¹ := by
    rw [← hgz]
    calc g * z * g⁻¹ * (g * a * g⁻¹) * (g * z * g⁻¹)⁻¹ = g * (z * a * z⁻¹) * g⁻¹ := by group
      _ = g * a⁻¹ * g⁻¹ := by rw [hza]
      _ = (g * a * g⁻¹)⁻¹ := by group
  constructor
  · intro h
    rw [h, hσa] at key
    exact hne key
  · intro h
    rw [h] at key
    have h2 : σ * a⁻¹ * σ⁻¹ = (σ * a * σ⁻¹)⁻¹ := by group
    rw [h2, hσa, inv_inv] at key
    exact hne key.symm

end Moves

theorem mulC_eq_mulE0 : ∀ a < 32, ∀ b < 32, mulC a b = mulE0 a b := by decide +kernel

section E0

variable {M : Type*} [Group M] {D E : Subgroup M} {eD : D ≃* DihedralGroup 4} {t : M}
  {eltE : ℕ → M}

namespace DECtx

variable [hW : (D ⊔ E).Normal] (hctx : DECtx D E eD t eltE)

include hctx

theorem lab_64 : labD eD eltE 64 = sElt eD 4 := by
  show sElt eD (decD 64) * eltE (64 % 32) = _
  rw [show decD 64 = 4 by decide, show 64 % 32 = 0 by norm_num, hctx.L.one, mul_one]

theorem lab_85 : labD eD eltE 85 = sElt eD 2 * sElt eD 4 := by
  show sElt eD (decD 85) * eltE (85 % 32) = _
  rw [show decD 85 = 4 by decide, show 85 % 32 = 21 by norm_num,
    show (21 : ℕ) = eT from rfl, hctx.L.at_tI, hctx.t_eq, sElt_mul eD (by norm_num) (by norm_num),
    sElt_mul eD (by norm_num) (by norm_num), show dMul 4 2 = 6 by decide,
    show dMul 2 4 = 6 by decide]

theorem adm_index {σ : M} (hσ2 : σ * σ = 1) (hσa : σ * sElt eD 1 * σ⁻¹ = sElt eD 1)
    (hσb : σ * sElt eD 4 * σ⁻¹ = sElt eD 2 * sElt eD 4)
    (hσE : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E)
    (hcard : Nat.card ↥(E ⊓ Subgroup.centralizer ({σ} : Set M)) = 8)
    (hx : ∃ x ∈ E, x ≠ 1 ∧ x ≠ t ∧ x * x = 1 ∧ σ * x = x * σ) :
    ∃ i < 60, ((hctx.Phi σ : ↥Pg) : Equiv.Perm (Fin 128)) = permOfArr 128 admArr[i]! := by
  classical
  set ψ : Equiv.Perm (Fin 128) := ((hctx.Phi σ : ↥Pg) : Equiv.Perm (Fin 128)) with hψdef
  have hψ : ∀ i : Fin 128, σ * labD eD eltE i * σ⁻¹ = labD eD eltE (ψ i : ℕ) :=
    fun i => (hctx.Phi_lab σ i).symm
  have hfixiff : ∀ c : Fin 128, ψ c = c ↔ labD eD eltE c * σ = σ * labD eD eltE c := by
    intro c
    constructor
    · intro h
      have h1 := hψ c
      rw [h] at h1
      calc labD eD eltE c * σ = σ * labD eD eltE c * σ⁻¹ * σ := by rw [h1]
        _ = σ * labD eD eltE c := by group
    · intro h
      have h1 : σ * labD eD eltE c * σ⁻¹ = labD eD eltE c := by
        calc σ * labD eD eltE c * σ⁻¹ = labD eD eltE c * σ * σ⁻¹ := by rw [h]
          _ = labD eD eltE c := by group
      rw [hψ c] at h1
      exact Fin.ext (hctx.lab_inj0 (Fin.is_lt _) (Fin.is_lt _) h1)
  have hAdm : AdmPred ψ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : hctx.Phi (σ * σ) = 1 := by rw [hσ2, map_one]
      rw [map_mul] at h1
      exact congrArg Subtype.val h1
    · have h1 : σ * labD eD eltE 32 * σ⁻¹ = labD eD eltE (ψ ⟨32, by norm_num⟩ : ℕ) :=
        hψ ⟨32, by norm_num⟩
      rw [hctx.lab_32, hσa, ← hctx.lab_32] at h1
      exact (hctx.lab_inj0 (by norm_num) (Fin.is_lt _) h1).symm
    · have h1 : σ * labD eD eltE 64 * σ⁻¹ = labD eD eltE (ψ ⟨64, by norm_num⟩ : ℕ) :=
        hψ ⟨64, by norm_num⟩
      rw [hctx.lab_64, hσb, ← hctx.lab_85] at h1
      exact (hctx.lab_inj0 (by norm_num) (Fin.is_lt _) h1).symm
    · intro c hc
      have hcE : labD eD eltE c ∈ E := (hctx.lab_mem_E c.2).2 hc
      have h1 := hσE _ hcE
      rw [hψ c] at h1
      exact (hctx.lab_mem_E (Fin.is_lt _)).1 h1
    ·
      have hbij : Function.Bijective
          (fun c : {c : Fin 128 // (c : ℕ) < 32 ∧ ψ c = c} =>
            (⟨labD eD eltE c, Subgroup.mem_inf.2 ⟨(hctx.lab_mem_E c.1.2).2 c.2.1,
              Subgroup.mem_centralizer_singleton_iff.2 ((hfixiff c.1).1 c.2.2)⟩⟩ :
              ↥(E ⊓ Subgroup.centralizer ({σ} : Set M)))) := by
        constructor
        · intro c c' hcc
          exact Subtype.ext (Fin.ext (hctx.lab_inj0 (Fin.is_lt _) (Fin.is_lt _)
            (congrArg Subtype.val hcc)))
        · rintro ⟨w, hw⟩
          obtain ⟨hwE, hwC⟩ := Subgroup.mem_inf.1 hw
          obtain ⟨k, hk, hkw⟩ := hctx.L.surj w hwE
          have hk128 : k < 128 := hk.trans (by norm_num)
          have hlab : labD eD eltE k = w := by rw [hctx.lab_E hk, hkw]
          refine ⟨⟨⟨k, hk128⟩, hk, ?_⟩, Subtype.ext hlab⟩
          rw [hfixiff]
          rw [Subgroup.mem_centralizer_singleton_iff] at hwC
          show labD eD eltE k * σ = σ * labD eD eltE k
          rw [hlab]
          exact hwC
      have h1 := Nat.card_congr (Equiv.ofBijective _ hbij)
      rw [hcard] at h1
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, h1]
    · obtain ⟨x, hxE, hx1, hxt, hxx, hxc⟩ := hx
      obtain ⟨k, hk, hkx⟩ := hctx.L.surj x hxE
      have hk128 : k < 128 := hk.trans (by norm_num)
      refine ⟨⟨k, hk128⟩, hk, ?_, ?_, ?_, ?_⟩
      · intro h0
        apply hx1
        rw [← hkx, show k = 0 from h0, hctx.L.one]
      · intro h21
        apply hxt
        rw [← hkx, show k = 21 from h21, show (21 : ℕ) = eT from rfl, hctx.L.at_tI]
      · have h1 : eltE (mulE0 k k) = 1 := by
          rw [hctx.L.mul k hk k hk, hkx, hxx]
        have h2 : mulE0 k k = 0 :=
          hctx.L.inj _ (hctx.L.lt k hk k hk) 0 (by norm_num) (by rw [h1, hctx.L.one])
        show mulC k k = 0
        rw [mulC_eq_mulE0 k hk k hk, h2]
      · rw [hfixiff]
        show labD eD eltE k * σ = σ * labD eD eltE k
        rw [hctx.lab_E hk, hkx]
        exact hxc.symm
  exact adm_complete (hctx.Phi σ) hAdm

theorem E0_spec {σ : M} (hσ2 : σ * σ = 1) (hσa : σ * sElt eD 1 * σ⁻¹ = sElt eD 1)
    (hσb : σ * sElt eD 4 * σ⁻¹ = sElt eD 2 * sElt eD 4)
    (hσE : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E)
    (hcard : Nat.card ↥(E ⊓ Subgroup.centralizer ({σ} : Set M)) = 8)
    (hx : ∃ x ∈ E, x ≠ 1 ∧ x ≠ t ∧ x * x = 1 ∧ σ * x = x * σ) :
    ∃ elt0 : ℕ → M,
      ELabelling ((D ⊔ E) ⊓ Subgroup.centralizer ({σ} : Set M)) t mulE0 eT elt0 ∧
      Nat.card ↥((D ⊔ E) ⊓ Subgroup.centralizer
        ((((D ⊔ E) ⊓ Subgroup.centralizer ({σ} : Set M) : Subgroup M)) : Set M)) = 8 := by
  classical
  set ψ : Equiv.Perm (Fin 128) := ((hctx.Phi σ : ↥Pg) : Equiv.Perm (Fin 128)) with hψdef
  have hψ : ∀ i : Fin 128, σ * labD eD eltE i * σ⁻¹ = labD eD eltE (ψ i : ℕ) :=
    fun i => (hctx.Phi_lab σ i).symm
  have hfixiff : ∀ c : Fin 128, ψ c = c ↔ labD eD eltE c * σ = σ * labD eD eltE c := by
    intro c
    constructor
    · intro h
      have h1 := hψ c
      rw [h] at h1
      calc labD eD eltE c * σ = σ * labD eD eltE c * σ⁻¹ * σ := by rw [h1]
        _ = σ * labD eD eltE c := by group
    · intro h
      have h1 : σ * labD eD eltE c * σ⁻¹ = labD eD eltE c := by
        calc σ * labD eD eltE c * σ⁻¹ = labD eD eltE c * σ * σ⁻¹ := by rw [h]
          _ = labD eD eltE c := by group
      rw [hψ c] at h1
      exact Fin.ext (hctx.lab_inj0 (Fin.is_lt _) (Fin.is_lt _) h1)
  obtain ⟨i, hi, hψi⟩ := hctx.adm_index hσ2 hσa hσb hσE hcard hx
  obtain ⟨hrep, hsz, h0, h21, hfix, hmul, hinj, hsurj⟩ := adm_facts hi
  have hψtab : ∀ c : Fin 128, (ψ c : ℕ) = (admArr[i]!)[(c : ℕ)]! := by
    intro c
    rw [hψdef, hψi]
    exact (hrep c).symm
  set F : ℕ → ℕ := fun k => (admIso[i]!)[k]! with hF
  have hFlt : ∀ k < 32, F k < 128 := fun k hk => (hfix k hk).1
  have hFfix : ∀ k, ∀ hk : k < 32, ψ ⟨F k, hFlt k hk⟩ = ⟨F k, hFlt k hk⟩ := by
    intro k hk
    apply Fin.ext
    rw [hψtab]
    exact (hfix k hk).2
  have hlabF : ∀ k < 32, labD eD eltE (F k) * σ = σ * labD eD eltE (F k) := fun k hk =>
    (hfixiff ⟨F k, hFlt k hk⟩).1 (hFfix k hk)
  refine ⟨fun k => labD eD eltE (F k), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k hk
    exact Subgroup.mem_inf.2 ⟨hctx.lab_mem _ (hFlt k hk),
      Subgroup.mem_centralizer_singleton_iff.2 (hlabF k hk)⟩
  · intro w hw
    obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨c, hc, hcw⟩ := hctx.tabLab.surj w hwW
    rw [Subgroup.mem_centralizer_singleton_iff] at hwC
    have hcfix : ψ ⟨c, hc⟩ = ⟨c, hc⟩ := by
      rw [hfixiff]
      show labD eD eltE c * σ = σ * labD eD eltE c
      rw [hcw]
      exact hwC
    have htab : (admArr[i]!)[c]! = c := by
      have := hψtab ⟨c, hc⟩
      rw [hcfix] at this
      exact this.symm
    obtain ⟨k, hk, hkc⟩ := hsurj c hc htab
    exact ⟨k, hk, by rw [show F k = c from hkc, hcw]⟩
  · intro a ha b hb hab
    exact hinj a ha b hb (hctx.lab_inj0 (hFlt a ha) (hFlt b hb) hab)
  · exact hctx.L.lt
  · intro a ha b hb
    have hlt := hctx.L.lt a ha b hb
    show labD eD eltE (F (mulE0 a b)) = labD eD eltE (F a) * labD eD eltE (F b)
    have : F (mulE0 a b) = mulC (F a) (F b) := hmul a ha b hb
    rw [this, hctx.tabLab.mul _ (hFlt a ha) _ (hFlt b hb)]
  · show labD eD eltE (F 0) = 1
    rw [show F 0 = 0 from h0, hctx.lab_zero]
  · exact eT_lt
  · show labD eD eltE (F eT) = t
    rw [show F eT = tC from h21, hctx.lab_tC]
  ·
    have hbij : Function.Bijective
        (fun c : {c : Fin 128 // ∀ g : Fin 128, ψ g = g →
            mulC (c : ℕ) (g : ℕ) = mulC (g : ℕ) (c : ℕ)} =>
          (⟨labD eD eltE c, Subgroup.mem_inf.2 ⟨hctx.lab_mem _ c.1.2, by
            rw [Subgroup.mem_centralizer_iff]
            intro h hh
            obtain ⟨hhW, hhC⟩ := Subgroup.mem_inf.1 hh
            obtain ⟨g, hg, rfl⟩ := hctx.tabLab.surj h hhW
            rw [Subgroup.mem_centralizer_singleton_iff] at hhC
            have hgfix : ψ ⟨g, hg⟩ = ⟨g, hg⟩ := by
              rw [hfixiff]
              exact hhC
            have := c.2 ⟨g, hg⟩ hgfix
            rw [← hctx.tabLab.mul _ hg _ c.1.2, ← hctx.tabLab.mul _ c.1.2 _ hg]
            exact congrArg _ this.symm⟩⟩ :
            ↥((D ⊔ E) ⊓ Subgroup.centralizer
              ((((D ⊔ E) ⊓ Subgroup.centralizer ({σ} : Set M) : Subgroup M)) : Set M)))) := by
      constructor
      · intro c c' hcc
        exact Subtype.ext (Fin.ext (hctx.lab_inj0 (Fin.is_lt _) (Fin.is_lt _)
          (congrArg Subtype.val hcc)))
      · rintro ⟨w, hw⟩
        obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.1 hw
        obtain ⟨c, hc, hcw⟩ := hctx.tabLab.surj w hwW
        refine ⟨⟨⟨c, hc⟩, fun g hg => ?_⟩, Subtype.ext hcw⟩
        have hgE0 : labD eD eltE g ∈ (D ⊔ E) ⊓ Subgroup.centralizer ({σ} : Set M) :=
          Subgroup.mem_inf.2 ⟨hctx.lab_mem _ g.2,
            Subgroup.mem_centralizer_singleton_iff.2 ((hfixiff g).1 hg)⟩
        have h1 := Subgroup.mem_centralizer_iff.1 hwC _ hgE0
        rw [← hcw, ← hctx.tabLab.mul _ g.2 _ hc, ← hctx.tabLab.mul _ hc _ g.2] at h1
        exact (hctx.lab_inj0 (mulC_lt g.2 hc) (mulC_lt hc g.2) h1).symm
    have h1 := Nat.card_congr (Equiv.ofBijective _ hbij)
    have h2 := adm_cent_card hi
    rw [← hψi] at h2
    rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h2

end DECtx

end E0

end CFSG.EvenSporadicStandard.Fin76b.W16
