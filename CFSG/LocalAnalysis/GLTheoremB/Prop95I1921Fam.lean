module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Asm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921AutPerm

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open Equiv Equiv.Perm

section CombFamily

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def LocP (a s : Perm Ω) : Prop :=
  (∀ x, a x ≠ x → s x = x) ∧
    (s = 1 ∨ (fixF a).card = 2 ∨ ((fixF a).card = 4 ∧ IsDT (fixF a) s))

theorem LocP.mul {a s s' : Perm Ω} (hs : LocP a s) (hs' : LocP a s') : LocP a (s * s') := by
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [Perm.mul_apply]
    rw [hs'.1 x hx, hs.1 x hx]
  · by_cases h2 : (fixF a).card = 2
    · exact Or.inr (Or.inl h2)
    · by_cases h4 : (fixF a).card = 4
      · have key : ∀ t : Perm Ω, LocP a t → t ∈ V4 (fixF a) h4 := by
          intro t ht
          rcases ht.2 with h | h | ⟨-, h⟩
          · exact (mem_V4 h4).2 (Or.inl h)
          · exact absurd h h2
          · exact (mem_V4 h4).2 (Or.inr h)
        have hm : s * s' ∈ V4 (fixF a) h4 := (V4 (fixF a) h4).mul_mem (key s hs) (key s' hs')
        rcases (mem_V4 h4).1 hm with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨h4, h⟩)
      · left
        have hs1 : s = 1 := by
          rcases hs.2 with h | h | ⟨h, -⟩
          · exact h
          · exact absurd h h2
          · exact absurd h h4
        have hs1' : s' = 1 := by
          rcases hs'.2 with h | h | ⟨h, -⟩
          · exact h
          · exact absurd h h2
          · exact absurd h h4
        rw [hs1, hs1', one_mul]

variable {N : Type*} [Group N]

theorem comb_family {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Ψ : N →* Perm Ω) {Dn : Subgroup N}
    (hDc : ∀ a ∈ Dn, ∀ b ∈ Dn, a * b = b * a) (hDe : ∀ a ∈ Dn, a ^ p = 1)
    (Sg : N → Subgroup (Perm Ω))
    (hloc : ∀ d ∈ Dn, Ψ d ≠ 1 → ∀ s ∈ Sg d, LocP (Ψ d) s)
    (hinv : ∀ d ∈ Dn, Ψ d ≠ 1 → ∀ d' ∈ Dn, ∀ s ∈ Sg d, Ψ d' * s * (Ψ d')⁻¹ ∈ Sg d)
    {R : Subgroup (Perm Ω)} (hR2 : ∀ r ∈ R, ∃ m : ℕ, r ^ (2 ^ m) = 1)
    (hRS : R ≤ ⨆ (d : N) (_ : d ∈ Dn) (_ : Ψ d ≠ 1), Sg d)
    (hRn : ∀ s ∈ (⨆ (d : N) (_ : d ∈ Dn) (_ : Ψ d ≠ 1), Sg d), ∀ r ∈ R, s * r * s⁻¹ ∈ R) :
    R = ⊥ ∨ (∃ x y : Ω, x ≠ y ∧ R = Subgroup.zpowers (swap x y) ∧
        Fintype.card Ω ≡ 2 [MOD p]) ∨
      (Fintype.card Ω ≡ 4 [MOD p] ∧ ∃ F : Finset Ω, F.card = 4 ∧ ∀ r ∈ R, r = 1 ∨ IsDT F r) := by
  classical
  set W' : Subgroup (Perm Ω) := ⨆ (d : N) (_ : d ∈ Dn) (_ : Ψ d ≠ 1), Sg d with hW'
  let Δ : Subgroup (Perm Ω) := Dn.map Ψ
  let Sgf : Perm Ω → Subgroup (Perm Ω) := fun a => ⨆ (d : N) (_ : d ∈ Dn) (_ : Ψ d = a), Sg d
  have hSgf_le : ∀ d ∈ Dn, Sg d ≤ Sgf (Ψ d) := fun d hd =>
    le_iSup₂_of_le d hd (le_iSup_of_le rfl le_rfl)
  have hW'_le : ∀ d ∈ Dn, Ψ d ≠ 1 → Sg d ≤ W' := fun d hd hd1 =>
    le_iSup₂_of_le d hd (le_iSup_of_le hd1 le_rfl)
  have hSgf_W' : ∀ a : Perm Ω, a ≠ 1 → Sgf a ≤ W' := by
    intro a ha
    refine iSup_le fun d => iSup_le fun hd => iSup_le fun hda => ?_
    exact hW'_le d hd (by rw [hda]; exact ha)
  have hmemΔ : ∀ a ∈ Δ, ∃ d ∈ Dn, Ψ d = a := fun a ha => by
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 ha
    exact ⟨d, hd, rfl⟩
  have hjoin : (⨆ (a : Perm Ω) (_ : a ∈ Δ) (_ : a ≠ 1), Sgf a) = W' := by
    apply le_antisymm
    · refine iSup_le fun a => iSup_le fun _ => iSup_le fun ha1 => hSgf_W' a ha1
    · refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
      exact (hSgf_le d hd).trans
        (le_iSup₂_of_le (Ψ d) (Subgroup.mem_map_of_mem Ψ hd) (le_iSup_of_le hd1 le_rfl))
  refine comb hp hp2 (Δ := Δ) (Sg := Sgf) ?_ ?_ ?_ ?_ hR2 (hjoin ▸ hRS) (hjoin ▸ hRn)
  · intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := hmemΔ a ha
    obtain ⟨d', hd', rfl⟩ := hmemΔ b hb
    rw [← map_mul, ← map_mul, hDc d hd d' hd']
  · intro a ha
    obtain ⟨d, hd, rfl⟩ := hmemΔ a ha
    rw [← map_pow, hDe d hd, map_one]
  · intro a ha ha1 s hs
    refine Subgroup.iSup_induction (fun (d : N) => ⨆ (_ : d ∈ Dn) (_ : Ψ d = a), Sg d)
      (C := fun s => LocP a s) hs ?_ ⟨fun x _ => rfl, Or.inl rfl⟩ (fun s s' => LocP.mul)
    intro d s hs
    refine Subgroup.iSup_induction (fun (_ : d ∈ Dn) => ⨆ (_ : Ψ d = a), Sg d)
      (C := fun s => LocP a s) hs ?_ ⟨fun x _ => rfl, Or.inl rfl⟩ (fun s s' => LocP.mul)
    intro hd s hs
    refine Subgroup.iSup_induction (fun (_ : Ψ d = a) => Sg d)
      (C := fun s => LocP a s) hs ?_ ⟨fun x _ => rfl, Or.inl rfl⟩ (fun s s' => LocP.mul)
    intro hda s₀ hs₀
    have h1 := hloc d hd (by rw [hda]; exact ha1) s₀ hs₀
    rw [hda] at h1
    exact h1
  · intro a ha ha1 e he s hs
    obtain ⟨d', hd', rfl⟩ := hmemΔ e he
    refine Subgroup.iSup_induction (fun (d : N) => ⨆ (_ : d ∈ Dn) (_ : Ψ d = a), Sg d)
      (C := fun s => Ψ d' * s * (Ψ d')⁻¹ ∈ Sgf a) hs ?_ (by simp) ?_
    · intro d s hs
      refine Subgroup.iSup_induction (fun (_ : d ∈ Dn) => ⨆ (_ : Ψ d = a), Sg d)
        (C := fun s => Ψ d' * s * (Ψ d')⁻¹ ∈ Sgf a) hs ?_ (by simp) ?_
      · intro hd s hs
        refine Subgroup.iSup_induction (fun (_ : Ψ d = a) => Sg d)
          (C := fun s => Ψ d' * s * (Ψ d')⁻¹ ∈ Sgf a) hs ?_ (by simp) ?_
        · intro hda s₀ hs₀
          have h1 := hSgf_le d hd (hinv d hd (by rw [hda]; exact ha1) d' hd' s₀ hs₀)
          rw [hda] at h1
          exact h1
        · intro s s' hs hs'
          have : Ψ d' * (s * s') * (Ψ d')⁻¹ = (Ψ d' * s * (Ψ d')⁻¹) * (Ψ d' * s' * (Ψ d')⁻¹) := by
            group
          rw [this]
          exact (Sgf a).mul_mem hs hs'
      · intro s s' hs hs'
        have : Ψ d' * (s * s') * (Ψ d')⁻¹ = (Ψ d' * s * (Ψ d')⁻¹) * (Ψ d' * s' * (Ψ d')⁻¹) := by
          group
        rw [this]
        exact (Sgf a).mul_mem hs hs'
    · intro s s' hs hs'
      have : Ψ d' * (s * s') * (Ψ d')⁻¹ = (Ψ d' * s * (Ψ d')⁻¹) * (Ψ d' * s' * (Ψ d')⁻¹) := by
        group
      rw [this]
      exact (Sgf a).mul_mem hs hs'

end CombFamily

section FamMain

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

theorem sd_le_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsComponentOf K ⊤)
    (hO : GLAPPrimeCore p ↥K = ⊥) {d : X} (hd : d ^ p = 1) {Sd : Subgroup X}
    (hSd : Sd ≤ pCoreOf 2 (Subgroup.centralizer ({d} : Set X)))
    (hSdC : ∀ c ∈ Subgroup.centralizer ({d} : Set X), c ∈ Subgroup.normalizer (Sd : Set X))
    (h : ∀ hdN : d ∈ Subgroup.normalizer (K : Set X), K.normalizerMonoidHom ⟨d, hdN⟩ = 1) :
    Sd ≤ Subgroup.centralizer (K : Set X) := by
  by_cases hdN : d ∈ Subgroup.normalizer (K : Set X)
  · have hdC : d ∈ Subgroup.centralizer (K : Set X) :=
      (normalizerMonoidHom_eq_one_iff hdN).1 (h hdN)
    have hKC : K ≤ Subgroup.centralizer ({d} : Set X) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hdC k hk
    have hSdN : Sd ≤ Subgroup.normalizer (K : Set X) :=
      hSd.trans (pCoreOf_centralizer_singleton_le_normalizer hp hp2 hK hO hd)
    have hSd2 : ∀ s ∈ Sd, ∃ m : ℕ, s ^ (2 ^ m) = 1 := fun s hs => by
      obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
        (Subgroup.centralizer ({d} : Set X))) ⟨s, hSd hs⟩
      exact ⟨m, congrArg Subtype.val hm⟩
    exact le_centralizer_of_normalized_by hK hSd2 hSdN (fun k hk s hs =>
      (Subgroup.mem_normalizer_iff.1 (hSdC k (hKC hk)) s).1 hs)
  · exact le_centralizer_of_not_mem_normalizer hp hp2 hK hO hd hdN hSd

theorem le_zpowers_swap_cases {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {x y : Ω} {H : Subgroup (Perm Ω)}
    (hH : H ≤ Subgroup.zpowers (swap x y)) : H = ⊥ ∨ H = Subgroup.zpowers (swap x y) := by
  by_cases hτ : swap x y ∈ H
  · exact Or.inr (le_antisymm hH ((Subgroup.zpowers_le).2 hτ))
  · left
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_swap_cases (hH hr) with h | h
    · exact h
    · exact absurd (h ▸ hr) hτ

theorem fam_main (hH : HatSevenOddInverts) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : IsComponentOf K ⊤) (hO : GLAPPrimeCore p ↥K = ⊥)
    {n : ℕ} {e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin n))} (A : APD K e)
    (hZ : Subgroup.center ↥K = ⊥ ∨ (n = 7 ∧ Nat.card (Subgroup.center ↥K) = 3 ∧ p = 3))
    {D : Subgroup X} {Sd : X → Subgroup X} (hD : SignalizerFamily p D Sd)
    (hC : SignalizerFamily.CInvariant D Sd) {So : Subgroup X}
    (hSo : So ≤ pCoreOf 2 (sigmaFam D Sd)) :
    (inducedAutGroup So K).map A.θ = ⊥ ∨
      (∃ x y : Fin n, x ≠ y ∧ (inducedAutGroup So K).map A.θ = Subgroup.zpowers (swap x y) ∧
        n ≡ 2 [MOD p]) ∨
      (n ≡ 4 [MOD p] ∧ ∃ F : Finset (Fin n), F.card = 4 ∧
        ∀ r ∈ (inducedAutGroup So K).map A.θ, r = 1 ∨ IsDT F r) := by
  classical
  have hodd := center_no_two_elements hp hp2 hO
  have hDp : ∀ d ∈ D, d ^ p = 1 := hD.elemAbelian.2
  have hDc : ∀ d ∈ D, ∀ d' ∈ D, d * d' = d' * d := fun d hd d' hd' =>
    congrArg Subtype.val (hD.elemAbelian.1.is_comm.comm (⟨d, hd⟩ : D) ⟨d', hd'⟩)
  have hSdN : ∀ d ∈ D, d ≠ 1 → Sd d ≤ Subgroup.normalizer (K : Set X) := fun d hd hd1 =>
    (hD.le_pCore d hd hd1).trans
      (pCoreOf_centralizer_singleton_le_normalizer hp hp2 hK hO (hDp d hd))
  have hSdC : ∀ d ∈ D, d ≠ 1 → Sd d ≤ Subgroup.centralizer ({d} : Set X) := fun d hd hd1 =>
    (hD.le_pCore d hd hd1).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hSd2 : ∀ d ∈ D, d ≠ 1 → ∀ t ∈ Sd d, ∃ m : ℕ, t ^ (2 ^ m) = 1 := fun d hd hd1 t ht => by
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer ({d} : Set X))) ⟨t, hD.le_pCore d hd hd1 ht⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  set S := sigmaFam D Sd with hS
  have hSdle : ∀ d ∈ D, d ≠ 1 → Sd d ≤ S := fun d hd hd1 =>
    le_iSup₂_of_le d hd (le_iSup_of_le hd1 le_rfl)
  have hSN : S ≤ Subgroup.normalizer (K : Set X) :=
    iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => hSdN d hd hd1
  have hS2 : ∀ t ∈ pCoreOf 2 S, ∃ m : ℕ, t ^ (2 ^ m) = 1 := fun t ht => by
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S) ⟨t, ht⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  let Ψ : ↥(Subgroup.normalizer (K : Set X)) →* Perm (Fin n) :=
    A.θ.comp K.normalizerMonoidHom
  let Sg : ↥(Subgroup.normalizer (K : Set X)) → Subgroup (Perm (Fin n)) := fun d =>
    (inducedAutGroup (Sd (d : X)) K).map A.θ
  let R : Subgroup (Perm (Fin n)) := (inducedAutGroup (pCoreOf 2 S) K).map A.θ
  let Dn : Subgroup ↥(Subgroup.normalizer (K : Set X)) := D.subgroupOf _
  have hΨ : ∀ d : ↥(Subgroup.normalizer (K : Set X)), Ψ d = A.θ (K.normalizerMonoidHom d) :=
    fun d => rfl
  have hmemSg : ∀ (d : ↥(Subgroup.normalizer (K : Set X))) (s : Perm (Fin n)),
      s ∈ Sg d ↔ ∃ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ Sd (d : X) ∧
        Ψ ⟨t, ht⟩ = s := fun d s => mem_sig_iff A.θ (Sd (d : X))
  have hmemR : ∀ s : Perm (Fin n), s ∈ R ↔
      ∃ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ pCoreOf 2 S ∧ Ψ ⟨t, ht⟩ = s :=
    fun s => mem_sig_iff A.θ (pCoreOf 2 S)
  have hloc : ∀ d ∈ Dn, Ψ d ≠ 1 → ∀ s ∈ Sg d, LocP (Ψ d) s := by
    intro d hd hΨd s hs
    have hd1 : (d : X) ≠ 1 := by
      intro h
      apply hΨd
      have : d = 1 := Subtype.ext h
      rw [this, map_one]
    exact perm_data hH hp hp2 hK hodd A hZ (hDp d hd) d.2 hΨd (hSdC d hd hd1) (hSd2 d hd hd1)
      (hSdN d hd hd1) (hC d hd hd1) s hs
  have hinv : ∀ d ∈ Dn, Ψ d ≠ 1 → ∀ d' ∈ Dn, ∀ s ∈ Sg d, Ψ d' * s * (Ψ d')⁻¹ ∈ Sg d := by
    intro d hd hΨd d' hd' s hs
    have hd1 : (d : X) ≠ 1 := by
      intro h
      apply hΨd
      have : d = 1 := Subtype.ext h
      rw [this, map_one]
    obtain ⟨t, ht, htS, rfl⟩ := (hmemSg d s).1 hs
    have hconj : (d' : X) * t * (d' : X)⁻¹ ∈ Sd (d : X) :=
      (Subgroup.mem_normalizer_iff.1 (hD.inv_D (d : X) hd hd1 (d' : X) hd') t).1 htS
    have hconjN : (d' : X) * t * (d' : X)⁻¹ ∈ Subgroup.normalizer (K : Set X) :=
      hSdN d hd hd1 hconj
    refine (hmemSg d _).2 ⟨(d' : X) * t * (d' : X)⁻¹, hconjN, hconj, ?_⟩
    have : (⟨(d' : X) * t * (d' : X)⁻¹, hconjN⟩ : ↥(Subgroup.normalizer (K : Set X))) =
        d' * ⟨t, ht⟩ * d'⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv]
  have hR2 : ∀ r ∈ R, ∃ m : ℕ, r ^ (2 ^ m) = 1 := by
    intro r hr
    obtain ⟨t, ht, htS, rfl⟩ := (hmemR r).1 hr
    obtain ⟨m, hm⟩ := hS2 t htS
    refine ⟨m, ?_⟩
    have h1 : (⟨t, ht⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ (2 ^ m) = 1 := Subtype.ext hm
    rw [← map_pow, h1, map_one]
  set W' : Subgroup (Perm (Fin n)) := ⨆ (d : ↥(Subgroup.normalizer (K : Set X))) (_ : d ∈ Dn)
    (_ : Ψ d ≠ 1), Sg d with hW'
  have hHbig : ∀ t ∈ S, ∃ ht : t ∈ Subgroup.normalizer (K : Set X), Ψ ⟨t, ht⟩ ∈ W' := by
    have hle : S ≤ (W'.comap Ψ).map (Subgroup.normalizer (K : Set X)).subtype := by
      refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
      intro t ht
      have htN := hSdN d hd hd1 ht
      refine ⟨⟨t, htN⟩, ?_, rfl⟩
      show Ψ ⟨t, htN⟩ ∈ W'
      by_cases hpsi : ∃ hdN : d ∈ Subgroup.normalizer (K : Set X),
          K.normalizerMonoidHom ⟨d, hdN⟩ ≠ 1
      · obtain ⟨hdN, hρ⟩ := hpsi
        have hΨd : Ψ ⟨d, hdN⟩ ≠ 1 := fun h => hρ (A.inj (h.trans (map_one A.θ).symm))
        have hle' : Sg ⟨d, hdN⟩ ≤ W' :=
          le_iSup₂_of_le (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set X))) hd
            (le_iSup_of_le hΨd le_rfl)
        exact hle' ((hmemSg ⟨d, hdN⟩ _).2 ⟨t, htN, ht, rfl⟩)
      · push Not at hpsi
        have hcent := sd_le_centralizer hp hp2 hK hO (hDp d hd) (hD.le_pCore d hd hd1)
          (hC d hd hd1) hpsi
        have h1 : K.normalizerMonoidHom ⟨t, htN⟩ = 1 :=
          (normalizerMonoidHom_eq_one_iff htN).2 (hcent ht)
        show A.θ (K.normalizerMonoidHom ⟨t, htN⟩) ∈ W'
        rw [h1, map_one]
        exact W'.one_mem
    intro t ht
    obtain ⟨⟨t', ht'⟩, hmem, rfl⟩ := hle ht
    exact ⟨ht', hmem⟩
  have hRS : R ≤ W' := by
    intro r hr
    obtain ⟨t, ht, htS, rfl⟩ := (hmemR r).1 hr
    obtain ⟨ht', hmem⟩ := hHbig t (CFSG.LieType.BorelTits.pCoreOf_le 2 S htS)
    exact hmem
  have hW'le : ∀ s ∈ W', ∃ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ S ∧
      Ψ ⟨t, ht⟩ = s := by
    have hle : W' ≤ (inducedAutGroup S K).map A.θ := by
      refine iSup_le fun d => iSup_le fun hd => iSup_le fun hΨd => ?_
      have hd1 : (d : X) ≠ 1 := by
        intro h
        apply hΨd
        have : d = 1 := Subtype.ext h
        rw [this, map_one]
      intro s hs
      obtain ⟨t, ht, htS, rfl⟩ := (hmemSg d s).1 hs
      exact (mem_sig_iff A.θ S).2 ⟨t, ht, hSdle d hd hd1 htS, rfl⟩
    intro s hs
    exact (mem_sig_iff A.θ S).1 (hle hs)
  have hRn : ∀ s ∈ W', ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
    intro s hs r hr
    obtain ⟨t, ht, htS, rfl⟩ := hW'le s hs
    obtain ⟨u, hu, huS, rfl⟩ := (hmemR r).1 hr
    have huc : t * u * t⁻¹ ∈ pCoreOf 2 S :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 S htS) u).1 huS
    have hucN : t * u * t⁻¹ ∈ Subgroup.normalizer (K : Set X) :=
      hSN (CFSG.LieType.BorelTits.pCoreOf_le 2 S huc)
    refine (hmemR _).2 ⟨t * u * t⁻¹, hucN, huc, ?_⟩
    have : (⟨t * u * t⁻¹, hucN⟩ : ↥(Subgroup.normalizer (K : Set X))) =
        ⟨t, ht⟩ * ⟨u, hu⟩ * ⟨t, ht⟩⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv]
  have hcomb := comb_family hp hp2 Ψ (Dn := Dn) (fun a ha b hb => Subtype.ext (hDc a ha b hb))
    (fun a ha => Subtype.ext (hDp a ha)) Sg hloc hinv hR2 hRS hRn
  have hRo : (inducedAutGroup So K).map A.θ ≤ R := by
    intro s hs
    obtain ⟨t, ht, htSo, rfl⟩ := (mem_sig_iff A.θ So).1 hs
    exact (mem_sig_iff A.θ (pCoreOf 2 S)).2 ⟨t, ht, hSo htSo, rfl⟩
  rcases hcomb with h | ⟨x, y, hxy, hRz, hmod⟩ | ⟨hmod, F, hF, hRF⟩
  · left
    exact le_bot_iff.1 (h ▸ hRo)
  · have hRo' : (inducedAutGroup So K).map A.θ ≤ Subgroup.zpowers (swap x y) := hRz ▸ hRo
    rcases le_zpowers_swap_cases hRo' with h | h
    · left; exact h
    · right; left
      refine ⟨x, y, hxy, h, ?_⟩
      rwa [Fintype.card_fin] at hmod
  · right; right
    refine ⟨by rwa [Fintype.card_fin] at hmod, F, hF, fun r hr => hRF r (hRo hr)⟩

end FamMain

section Translate

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

theorem sigmaFam_le_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsComponentOf K ⊤)
    (hO : GLAPPrimeCore p ↥K = ⊥) {D : Subgroup X} {Sd : X → Subgroup X}
    (hD : SignalizerFamily p D Sd) : sigmaFam D Sd ≤ Subgroup.normalizer (K : Set X) :=
  iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 =>
    (hD.le_pCore d hd hd1).trans
      (pCoreOf_centralizer_singleton_le_normalizer hp hp2 hK hO (hD.elemAbelian.2 d hd))

theorem actsAsTransposition_of_perm {p k : ℕ} (hk : 0 < k) (hZ : Subgroup.center ↥K = ⊥)
    {e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin (k * p + 2)))} (A : APD K e)
    {So : Subgroup X} {x y : Fin (k * p + 2)} (hxy : x ≠ y)
    (hR : (inducedAutGroup So K).map A.θ = Subgroup.zpowers (swap x y)) :
    ActsAsTransposition p So K := by
  refine ⟨k, hk, ?_⟩
  let e' : ↥K ≃* ↥(alternatingGroup (Fin (k * p + 2))) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hmk : ∀ a : ↥K, e' a = e (QuotientGroup.mk a) := fun a => rfl
  have hcongr : ∀ φ : MulAut ↥K, MulAut.congr e' φ =
      MulAut.conjNormal (H := alternatingGroup (Fin (k * p + 2))) (A.θ φ) := by
    intro φ
    apply MulEquiv.ext
    intro g
    obtain ⟨a, rfl⟩ := e'.surjective g
    have h1 := A.ind φ a
    have h2 : (MulAut.congr e' φ) (e' a) = e' (φ a) := by
      simp [MulAut.congr_apply]
    rw [h2, hmk, hmk]
    exact h1
  have hswap : (swap x y).IsSwap := ⟨x, y, hxy, rfl⟩
  have hcard : Nat.card (inducedAutGroup So K) = 2 := by
    have h1 := Subgroup.card_map_of_injective (K := inducedAutGroup So K) A.inj
    rw [hR, Nat.card_zpowers, hswap.orderOf] at h1
    exact h1.symm
  refine ⟨e', swap x y, hswap, hcard, ?_⟩
  have hhom : (MulAut.congr e').toMonoidHom =
      (MulAut.conjNormal (H := alternatingGroup (Fin (k * p + 2)))).comp A.θ :=
    MonoidHom.ext fun φ => hcongr φ
  show (inducedAutGroup So K).map (MulAut.congr e').toMonoidHom =
    Subgroup.zpowers (MulAut.conjNormal (swap x y))
  rw [hhom, ← Subgroup.map_map, hR, MonoidHom.map_zpowers]

theorem actsLikeSubRootFourCQ_of_perm {n : ℕ}
    {e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin n))} (A : APD K e)
    {So : Subgroup X} {F : Finset (Fin n)} (hF : F.card = 4)
    (hR : ∀ r ∈ (inducedAutGroup So K).map A.θ, r = 1 ∨ IsDT F r) :
    ActsLikeSubRootFourCQ So K n e := by
  let V₄ : Subgroup ↥(alternatingGroup (Fin n)) :=
    (V4 F hF).comap (alternatingGroup (Fin n)).subtype
  let V : Subgroup ↥(alternatingGroup (Fin n)) :=
    ((inducedAutGroup So K).map A.θ).comap (alternatingGroup (Fin n)).subtype
  have hV₄ : IsRootFour V₄ := isRootFour_of_V4 hF V₄ (fun g => Iff.rfl)
  refine ⟨V₄, V, hV₄, ?_, ?_⟩
  · intro g hg
    exact (mem_V4 hF).2 (hR _ hg)
  · unfold ActsLikeCQ
    constructor
    · intro φ hφ
      obtain ⟨t, ht, htSo, rfl⟩ := mem_inducedAutGroup.1 hφ
      have hs : A.θ (K.normalizerMonoidHom ⟨t, ht⟩) ∈ (inducedAutGroup So K).map A.θ :=
        (mem_sig_iff A.θ So).2 ⟨t, ht, htSo, rfl⟩
      have hsev : sign (A.θ (K.normalizerMonoidHom ⟨t, ht⟩)) = 1 :=
        V4_sign hF ((mem_V4 hF).2 (hR _ hs))
      refine ⟨MulAut.conj (⟨_, Perm.mem_alternatingGroup.2 hsev⟩ : ↥(alternatingGroup (Fin n))),
        ⟨⟨_, Perm.mem_alternatingGroup.2 hsev⟩, hs, rfl⟩, ?_⟩
      rw [← MulAut.conjNormal_val]
      exact A.ind _
    · intro σ hσ
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hσ
      obtain ⟨t, ht, htSo, hgt⟩ := (mem_sig_iff A.θ So).1 hg
      refine ⟨K.normalizerMonoidHom ⟨t, ht⟩, mem_inducedAutGroup.2 ⟨t, ht, htSo, rfl⟩, ?_⟩
      have hgt' : A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = (g : Perm (Fin n)) := hgt
      rw [← MulAut.conjNormal_val, ← hgt']
      exact A.ind _

end Translate

section TwoNeSix

variable {X : Type} [Group X] [Finite X]

theorem input19_21_2_ne6 (hH : HatSevenOddInverts) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hO : GLAPPrimeCore p ↥K = ⊥) {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin n)))
    {D : Subgroup X} {Sd : X → Subgroup X} (hD : SignalizerFamily p D Sd)
    (hC : SignalizerFamily.CInvariant D Sd) {So : Subgroup X}
    (hSo : So ≤ pCoreOf 2 (sigmaFam D Sd)) :
    So ≤ Subgroup.centralizer (K : Set X) ∨ ActsAsTransposition p So K ∨
      (∃ (k : ℕ) (e' : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin (k * p + 4)))),
        ActsLikeSubRootFourCQ So K (k * p + 4) e') := by
  have hKq := isQuasisimple_of_comp hK
  have hZ := center_cases hp hp2 hKq hO hn hn6 e
  obtain ⟨θ, hθinj, hθind, hθinn⟩ := exists_autToPerm_of_perfect hK.2.2.1 hn hn6 e
  obtain ⟨A⟩ : Nonempty (APD K e) := ⟨⟨θ, hθinj, hθind, hθinn⟩⟩
  have hSoN : So ≤ Subgroup.normalizer (K : Set X) :=
    (hSo.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans
      (sigmaFam_le_normalizer hp hp2 hK hO hD)
  rcases fam_main hH hp hp2 hK hO A hZ hD hC hSo with h | ⟨x, y, hxy, hR, hmod⟩ |
    ⟨hmod, F, hF, hRF⟩
  · left
    exact (inducedAutGroup_eq_bot_iff hSoN).1 ((Subgroup.map_eq_bot_iff_of_injective _ A.inj).1 h)
  · right; left
    obtain ⟨k, hk⟩ : ∃ k, n = k * p + 2 := by
      obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (by omega : 2 ≤ n)).1 hmod.symm
      rw [mul_comm] at hk
      exact ⟨k, by omega⟩
    subst hk
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; omega
      · exact h0
    have hZ1 : Subgroup.center ↥K = ⊥ := by
      rcases hZ with hZ | ⟨h7, -, rfl⟩
      · exact hZ
      · omega
    exact actsAsTransposition_of_perm hk0 hZ1 A hxy hR
  · right; right
    obtain ⟨k, hk⟩ : ∃ k, n = k * p + 4 := by
      obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (by omega : 4 ≤ n)).1 hmod.symm
      rw [mul_comm] at hk
      exact ⟨k, by omega⟩
    subst hk
    exact ⟨k, e, actsLikeSubRootFourCQ_of_perm A hF hRF⟩

end TwoNeSix

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
