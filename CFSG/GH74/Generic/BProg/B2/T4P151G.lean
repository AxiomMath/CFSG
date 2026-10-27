module

public import CFSG.GH74.Generic.BProg.B2.T4P151Model
public import CFSG.GH74.Generic.BProg.B2.T4B3aG
public import CFSG.GH74.Generic.BProg.B2.T3S1Done
public import CFSG.GH74.Generic.BProg.B3.S3Sec29H

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.P151G

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup
open CFSG.GH74.Generic.BProg.B2.T4.P151Model

section Lift

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
theorem mk_eq_mk_iff {m m' : ↥M} :
    QuotientGroup.mk' (pPrimeCore 2 ↥M) m = QuotientGroup.mk' (pPrimeCore 2 ↥M) m' ↔
      (m : G)⁻¹ * m' ∈ pPrimeCoreOf 2 M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨m⁻¹ * m', h, by simp⟩
  · rintro ⟨n, hn, hn'⟩
    have : n = m⁻¹ * m' := Subtype.ext (by simpa using hn')
    rw [← this]
    exact hn

omit [Finite G] in
theorem mem_normalizer_pPrimeCoreOf {k : G} (hk : k ∈ M) :
    k ∈ normalizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun o => ⟨fun ho => TwoThin.pPrimeCoreOf_normalized M hk ho, fun ho => ?_⟩
  have := TwoThin.pPrimeCoreOf_normalized M (M.inv_mem hk) ho
  simpa [mul_assoc] using this

theorem exists_lift_comm' {P : Subgroup G} (hP : IsPGroup 2 ↥P) (hPM : P ≤ M) (z : Mbar M)
    (hc : ∀ (p : G) (hp : p ∈ P), QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p, hPM hp⟩ * z =
      z * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p, hPM hp⟩) :
    ∃ w : G, ∃ hw : w ∈ M, QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨w, hw⟩ = z ∧ ∀ p ∈ P, p * w = w * p := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) z
  have hN : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := TwoThin.card_pPrimeCoreOf_odd M
  have hPN : P ≤ normalizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) :=
    fun p hp => mem_normalizer_pPrimeCoreOf (hPM hp)
  have hg : ∀ p ∈ P, (g : G)⁻¹ * (p * g * p⁻¹) ∈ pPrimeCoreOf 2 M := by
    intro p hp
    have hpg : p * (g : G) * p⁻¹ ∈ M := M.mul_mem (M.mul_mem (hPM hp) g.2) (M.inv_mem (hPM hp))
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) g =
        QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p * (g : G) * p⁻¹, hpg⟩ := by
      have e : (⟨p * (g : G) * p⁻¹, hpg⟩ : ↥M) = ⟨p, hPM hp⟩ * g * ⟨p, hPM hp⟩⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, hc p hp, map_inv]
      group
    exact mk_eq_mk_iff.1 h1
  obtain ⟨w, hwN, hwP⟩ := B3.S3Sec29H.exists_fixed_mem_coset hP hN hPN hg
  have hwM : w ∈ M := by
    have e : w = (g : G) * ((g : G)⁻¹ * w) := by group
    rw [e]
    exact M.mul_mem g.2 (TwoThin.pPrimeCoreOf_le M hwN)
  refine ⟨w, hwM, ?_, hwP⟩
  exact (mk_eq_mk_iff.2 hwN).symm

theorem exists_lift_comm {P : Subgroup G} (hP : IsPGroup 2 ↥P) (hPM : P ≤ M) (z : Mbar M) (hzz : z * z = 1)
    (hc : ∀ (p : G) (hp : p ∈ P), QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p, hPM hp⟩ * z =
      z * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p, hPM hp⟩) :
    ∃ w : G, ∃ hw : w ∈ M, QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨w, hw⟩ = z ∧ w * w = 1 ∧
      ∀ p ∈ P, p * w = w * p := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) z
  have hN : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := TwoThin.card_pPrimeCoreOf_odd M
  have hPN : P ≤ normalizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) :=
    fun p hp => mem_normalizer_pPrimeCoreOf (hPM hp)
  have hg : ∀ p ∈ P, (g : G)⁻¹ * (p * g * p⁻¹) ∈ pPrimeCoreOf 2 M := by
    intro p hp
    have hpg : p * (g : G) * p⁻¹ ∈ M := M.mul_mem (M.mul_mem (hPM hp) g.2) (M.inv_mem (hPM hp))
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) g =
        QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p * (g : G) * p⁻¹, hpg⟩ := by
      have e : (⟨p * (g : G) * p⁻¹, hpg⟩ : ↥M) = ⟨p, hPM hp⟩ * g * ⟨p, hPM hp⟩⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, hc p hp, map_inv]
      group
    exact mk_eq_mk_iff.1 h1
  have hg2 : (g : G) * g ∈ pPrimeCoreOf 2 M := by
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) (g * g)⁻¹ = QuotientGroup.mk' (pPrimeCore 2 ↥M) 1 := by
      rw [map_inv, map_mul, hzz, inv_one, map_one]
    have := mk_eq_mk_iff.1 h1
    simpa using this
  obtain ⟨w, hwN, hww, hwP⟩ := B3.S3Sec29H.exists_inv_fixed_mem_coset hP hN hPN
    (mem_normalizer_pPrimeCoreOf g.2) hg2 hg
  have hwM : w ∈ M := by
    have e : w = (g : G) * ((g : G)⁻¹ * w) := by group
    rw [e]
    exact M.mul_mem g.2 (TwoThin.pPrimeCoreOf_le M hwN)
  exact ⟨w, hwM, (mk_eq_mk_iff.2 hwN).symm, hww, hwP⟩

end Lift

section Frame

variable {G : Type} [Group G] [Finite G]

structure Frame151 (M : Subgroup G) (a s : G) (I : Subgroup G) (e₁ e₂ : G) : Prop where
  aM : a ∈ M
  aa : a * a = 1
  a1 : a ≠ 1
  sM : s ∈ M
  ss : s * s = 1
  s1 : s ≠ 1
  sa : s * a = a * s
  Cs : centralizer ({s} : Set G) ≤ M
  Cas : centralizer ({a * s} : Set G) ≤ M
  Icomp : IsPCompIn 2 (centralizer ({s} : Set G) ⊓ centralizer ({a} : Set G)) I
  e₁I : e₁ ∈ I
  e₂I : e₂ ∈ I
  e₁e₁ : e₁ * e₁ = 1
  e₂e₂ : e₂ * e₂ = 1
  e₁e₂ : e₁ * e₂ = e₂ * e₁
  e₁1 : e₁ ≠ 1
  e₂1 : e₂ ≠ 1
  e₁₂ : e₁ ≠ e₂
  Ce₁ : centralizer ({a * e₁} : Set G) ≤ M
  Ce₂ : centralizer ({a * e₂} : Set G) ≤ M
  Ce₁₂ : centralizer ({a * (e₁ * e₂)} : Set G) ≤ M
  CE : centralizer ((zpowers e₁ ⊔ zpowers e₂ : Subgroup G) : Set G) ≤ M

@[expose] def Frame151Type (I : Subgroup G) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (f : ↥I →* Q), Function.Surjective f ∧ Odd (Nat.card f.ker) ∧
    IsQuasisimple Q ∧ IsL3OddSD (Q ⧸ center Q) ∧ ∀ z : Q, z ∈ center Q → z * z = 1 → z = 1

omit [Finite G] in
theorem mem_zpowers_invol {e h : G} (he : e * e = 1) (hh : h ∈ zpowers e) : h = 1 ∨ h = e := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have he2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact he
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · left; rw [zpow_mul, he2, one_zpow]
  · right; rw [zpow_add, zpow_mul, he2, one_zpow, one_mul, zpow_one]

omit [Finite G] in
theorem mem_four {e₁ e₂ v : G} (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1) (h₁₂ : e₁ * e₂ = e₂ * e₁)
    (hv : v ∈ zpowers e₁ ⊔ zpowers e₂) : v = 1 ∨ v = e₁ ∨ v = e₂ ∨ v = e₁ * e₂ := by
  have hc : ∀ h ∈ zpowers e₁, h * e₂ = e₂ * h := by
    intro h hh
    rcases mem_zpowers_invol h₁ hh with rfl | rfl
    · simp
    · exact h₁₂
  obtain ⟨h, hh, rfl | rfl⟩ := B3.S3Sec29H.mem_sup_zpowers h₂ hc hv
  · rcases mem_zpowers_invol h₁ hh with rfl | rfl
    · left; rfl
    · right; left; rfl
  · rcases mem_zpowers_invol h₁ hh with rfl | rfl
    · right; right; left; simp
    · right; right; right; rfl

omit [Finite G] in
theorem isElementaryAbelian_zpowers_invol {e : G} (he : e * e = 1) :
    CFSG.IsElementaryAbelian 2 ↥(zpowers e) :=
  B3.S3Sec29H.isElementaryAbelian_zpowers he

omit [Finite G] in
theorem card_four {e₁ e₂ : G} (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1) (h₁₂ : e₁ * e₂ = e₂ * e₁)
    (h₁1 : e₁ ≠ 1) (h₂1 : e₂ ≠ 1) (hne : e₁ ≠ e₂) : Nat.card ↥(zpowers e₁ ⊔ zpowers e₂) = 4 := by
  have hc : ∀ h ∈ zpowers e₁, h * e₂ = e₂ * h := by
    intro h hh
    rcases mem_zpowers_invol h₁ hh with rfl | rfl
    · simp
    · exact h₁₂
  have hnot : e₂ ∉ zpowers e₁ := by
    intro h
    rcases mem_zpowers_invol h₁ h with h | h
    · exact h₂1 h
    · exact hne h.symm
  rw [B3.S3Sec29H.card_sup_zpowers h₂ hnot hc]
  have h1 : orderOf e₁ = 2 := orderOf_eq_prime (by rw [sq]; exact h₁) h₁1
  rw [Nat.card_zpowers, h1]

theorem inU0C_frame {M : Subgroup G} {a s : G} {I : Subgroup G} {e₁ e₂ : G} (hF : Frame151 M a s I e₁ e₂)
    (hMtop : M ≠ ⊤) :
    InU0C M ((zpowers e₁ ⊔ zpowers e₂) ⊔ zpowers a) ∧
      Nat.card ↥((zpowers e₁ ⊔ zpowers e₂) ⊔ zpowers a) = 8 := by
  set V := zpowers e₁ ⊔ zpowers e₂ with hVdef
  have hIa : I ≤ centralizer ({a} : Set G) := hF.Icomp.1.trans inf_le_right
  have he₁a : e₁ * a = a * e₁ := Subgroup.mem_centralizer_singleton_iff.1 (hIa hF.e₁I)
  have he₂a : e₂ * a = a * e₂ := Subgroup.mem_centralizer_singleton_iff.1 (hIa hF.e₂I)
  have hVa : ∀ h ∈ V, h * a = a * h := by
    intro h hh
    rcases mem_four hF.e₁e₁ hF.e₂e₂ hF.e₁e₂ hh with rfl | rfl | rfl | rfl
    · simp
    · exact he₁a
    · exact he₂a
    · calc e₁ * e₂ * a = e₁ * (a * e₂) := by rw [mul_assoc, he₂a]
        _ = a * (e₁ * e₂) := by rw [← mul_assoc, he₁a, mul_assoc]
  have hcentM : ∀ v : G, centralizer ({v} : Set G) ≤ M → v ≠ 1 := by
    rintro v hv rfl
    apply hMtop
    rw [eq_top_iff]
    intro g _
    exact hv (Subgroup.mem_centralizer_singleton_iff.2 (by simp))
  have haV : a ∉ V := by
    intro haV
    rcases mem_four hF.e₁e₁ hF.e₂e₂ hF.e₁e₂ haV with h | h | h | h
    · exact hF.a1 h
    · exact hcentM _ hF.Ce₁ (by rw [h, hF.e₁e₁])
    · exact hcentM _ hF.Ce₂ (by rw [h, hF.e₂e₂])
    · apply hcentM _ hF.Ce₁₂
      rw [h]
      calc e₁ * e₂ * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by group
        _ = e₁ * (e₁ * e₂) * e₂ := by rw [hF.e₁e₂]
        _ = (e₁ * e₁) * (e₂ * e₂) := by group
        _ = 1 := by rw [hF.e₁e₁, hF.e₂e₂, one_mul]
  have hV4 : Nat.card ↥V = 4 := card_four hF.e₁e₁ hF.e₂e₂ hF.e₁e₂ hF.e₁1 hF.e₂1 hF.e₁₂
  have hc₁₂ : ∀ h ∈ zpowers e₁, h * e₂ = e₂ * h := by
    intro h hh
    rcases mem_zpowers_invol hF.e₁e₁ hh with rfl | rfl
    · simp
    · exact hF.e₁e₂
  have hVel : CFSG.IsElementaryAbelian 2 ↥V :=
    B3.S3Sec29H.isElementaryAbelian_sup_zpowers (isElementaryAbelian_zpowers_invol hF.e₁e₁) hF.e₂e₂ hc₁₂
  have hB8 : Nat.card ↥(V ⊔ zpowers a) = 8 := by
    rw [B3.S3Sec29H.card_sup_zpowers hF.aa haV hVa, hV4]
  have hBel : CFSG.IsElementaryAbelian 2 ↥(V ⊔ zpowers a) :=
    B3.S3Sec29H.isElementaryAbelian_sup_zpowers hVel hF.aa hVa
  have hIM : I ≤ M := hF.Icomp.1.trans (inf_le_left.trans hF.Cs)
  have hBM : V ⊔ zpowers a ≤ M := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (Subgroup.zpowers_le).2 (hIM hF.e₁I)
    · exact (Subgroup.zpowers_le).2 (hIM hF.e₂I)
    · exact (Subgroup.zpowers_le).2 hF.aM
  refine ⟨inU0C_of_four_subgroups hBM hBel hB8 (fun D hDB hD4 => ?_), hB8⟩
  by_cases hDV : D ≤ V
  · have hDeq : D = V := Subgroup.eq_of_le_of_card_ge hDV (by rw [hV4, hD4])
    rw [hDeq]
    exact hF.CE
  · obtain ⟨d, hdD, hdV⟩ := IsConcreteLE.not_le_iff_exists.1 hDV
    obtain ⟨v, hvV, hdv⟩ := B3.S3Sec29H.mem_sup_zpowers hF.aa hVa (hDB hdD)
    have hcard := B3.S3Sec29H.card_inf_le_two_mul (H := V ⊔ zpowers a) (H' := V) (X := D) le_sup_left
      (by rw [hB8, hV4])
    rw [inf_eq_right.2 hDB, hD4] at hcard
    have hne : ∃ w' ∈ V ⊓ D, w' ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : V ⊓ D = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
      rw [hbot, Subgroup.card_bot] at hcard
      omega
    obtain ⟨w', hw'VD, hw'1⟩ := hne
    have key : ∃ w ∈ V, w ≠ 1 ∧ a * w ∈ D := by
      rcases hdv with rfl | rfl
      · exact absurd hvV hdV
      · by_cases hv1 : v = 1
        · subst hv1
          rw [one_mul] at hdD
          exact ⟨w', hw'VD.1, hw'1, D.mul_mem hdD hw'VD.2⟩
        · refine ⟨v, hvV, hv1, ?_⟩
          rw [← hVa v hvV]
          exact hdD
    obtain ⟨w, hwV, hw1, hawD⟩ := key
    have hCD : centralizer (D : Set G) ≤ centralizer ({a * w} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hawD)
    refine hCD.trans ?_
    rcases mem_four hF.e₁e₁ hF.e₂e₂ hF.e₁e₂ hwV with rfl | rfl | rfl | rfl
    · exact absurd rfl hw1
    · exact hF.Ce₁
    · exact hF.Ce₂
    · exact hF.Ce₁₂

theorem conj_mem_pLayerOf {C : Subgroup G} {c l : G} (hc : c ∈ C) (hl : l ∈ pLayerOf 2 C) :
    c * l * c⁻¹ ∈ pLayerOf 2 C := by
  have hCc : C.map (MulAut.conj c).toMonoidHom = C := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact C.mul_mem (C.mul_mem hc hz) (C.inv_mem hc)
    · intro hy
      refine ⟨c⁻¹ * y * c, C.mul_mem (C.mul_mem (C.inv_mem hc) hy) hc, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hle : (pLayerOf 2 C).map (MulAut.conj c).toMonoidHom ≤ pLayerOf 2 C := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h1 := Stage1.Thm2.Recip.isPCompIn_map_conj hK c
    rw [hCc] at h1
    exact le_sSup h1
  exact hle ⟨l, hl, by simp [MulAut.conj_apply]⟩

theorem centralizer_le_of_frame {M : Subgroup G} {a s : G} {I : Subgroup G} {e₁ e₂ : G}
    (hF : Frame151 M a s I e₁ e₂) (hMtop : M ≠ ⊤) (h2C : Stage2Concl2C M)
    (hO : pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≤ M)
    (hL : pLayerOf 2 (centralizer ({a} : Set G)) ≤ M) : centralizer ({a} : Set G) ≤ M := by
  obtain ⟨hB, -⟩ := inU0C_frame hF hMtop
  set C := centralizer ({a} : Set G) with hC
  set N : Subgroup G := (zpowers a ⊔ pPrimeCoreOf 2 C) ⊔ pLayerOf 2 C with hN
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hNC : N ≤ C := sup_le (sup_le ((Subgroup.zpowers_le).2 haC) (TwoThin.pPrimeCoreOf_le C))
    (TwoThin.pLayerOf_le 2 C)
  have hconj : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    have hca : c * a * c⁻¹ = a := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hc
      rw [this]
      group
    have hmap : N.map (MulAut.conj c).toMonoidHom ≤ N := by
      rw [hN, Subgroup.map_sup, Subgroup.map_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [MonoidHom.map_zpowers]
        have : (MulAut.conj c).toMonoidHom a = a := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact hca
        rw [this]
        exact le_sup_left.trans le_sup_left
      · rintro _ ⟨o, ho, rfl⟩
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact TwoThin.pPrimeCoreOf_normalized C hc ho))
      · rintro _ ⟨l, hl, rfl⟩
        exact Subgroup.mem_sup_right (by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact conj_mem_pLayerOf hc hl)
    exact hmap ⟨n, hn, by simp [MulAut.conj_apply]⟩
  have hNn : (N.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hconj g g.2 n hn
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hF.ss) hF.s1
  have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hF.sa
  have hIL : I ≤ pLayerOf 2 C := Stage1.Thm2.Recip.le_pLayerOf_of_isPCompIn_inf hs2 hsC hF.Icomp
  have hBN : (zpowers e₁ ⊔ zpowers e₂) ⊔ zpowers a ≤ N := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (Subgroup.zpowers_le).2 (Subgroup.mem_sup_right (hIL hF.e₁I))
    · exact (Subgroup.zpowers_le).2 (Subgroup.mem_sup_right (hIL hF.e₂I))
    · exact le_sup_left.trans le_sup_left
  have hNM : N ≤ M := sup_le (sup_le ((Subgroup.zpowers_le).2 hF.aM) hO) hL
  exact le_M_of_normal_of_inU0C h2C hB hNC hNn hBN hNM

end Frame

section Conj

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf₀ {J₁ J₂ : Subgroup G} (hN : J₂ ≤ normalizer (J₁ : Set G)) :
    Nat.card ↥(J₁ ⊔ J₂) * Nat.card ↥(J₁ ⊓ J₂) = Nat.card ↥J₁ * Nat.card ↥J₂ := by
  set H : Subgroup G := J₁ ⊔ J₂ with hH
  have h₁ : J₁ ≤ H := le_sup_left
  have h₂ : J₂ ≤ H := le_sup_right
  set A : Subgroup ↥H := J₁.subgroupOf H with hA
  set B : Subgroup ↥H := J₂.subgroupOf H with hB
  have hAn : A.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h₁).2 (sup_le Subgroup.le_normalizer hN)
  have hsup : B ⊔ A = ⊤ := by
    rw [hA, hB, ← Subgroup.subgroupOf_sup h₂ h₁, sup_comm, ← hH, Subgroup.subgroupOf_self]
  have e1 : A.relIndex (B ⊔ A) = A.relIndex B := Subgroup.relIndex_sup_right B A
  rw [hsup] at e1
  have e2 := Subgroup.relIndex_mul_card A (⊤ : Subgroup ↥H)
  have e3 := Subgroup.relIndex_mul_card A B
  rw [inf_top_eq, Subgroup.card_top, e1] at e2
  have cA : Nat.card ↥A = Nat.card ↥J₁ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv
  have cB : Nat.card ↥B = Nat.card ↥J₂ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv
  have cI : Nat.card ↥(A ⊓ B) = Nat.card ↥(J₁ ⊓ J₂) := by
    have hinf : (J₁ ⊓ J₂).subgroupOf H = J₁.subgroupOf H ⊓ J₂.subgroupOf H := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hA, hB, ← hinf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h₁)).toEquiv
  rw [← cA, ← cB, ← cI, ← e2, ← e3]
  ring

theorem isSylowOf_of_card₀ {K X : Subgroup G} (hXK : X ≤ K) (hX : IsPGroup 2 ↥X) {m : ℕ}
    (hcard : Nat.card ↥X * m = Nat.card ↥K) (hm : ¬ 2 ∣ m) : CFSG.ABGLocalTools.IsSylowOf 2 X K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXk : IsPGroup 2 ↥(X.subgroupOf K) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hidx : (X.subgroupOf K).index = m := by
    have h1 := Subgroup.card_mul_index (X.subgroupOf K)
    have h2 : Nat.card ↥(X.subgroupOf K) = Nat.card ↥X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv
    rw [h2] at h1
    have hpos : 0 < Nat.card ↥X := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hcard.symm)
  refine ⟨hXk.toSylow (by rw [hidx]; exact hm), ?_⟩
  exact Subgroup.map_subgroupOf_eq_of_le hXK

theorem exists_conj_le_sylow₀ {K P E : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 2 P K) (hEK : E ≤ K)
    (hE : IsPGroup 2 ↥E) : ∃ k ∈ K, ∀ x ∈ E, k * x * k⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE' : IsPGroup 2 ↥(E.subgroupOf K) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  have hQK : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup ↥K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hQK.exists_mem_conj hP
  refine ⟨k, hk, fun x hx => ?_⟩
  rw [hconj]
  have : k⁻¹ * (k * x * k⁻¹) * k = x := by group
  rw [this]
  exact ⟨⟨x, hEK hx⟩, hQ hx, rfl⟩

theorem exists_conj_into {M A V : Subgroup G} (hAM : A ≤ M) (hA2 : IsPGroup 2 ↥A) (hV2 : IsPGroup 2 ↥V)
    (hV : ∀ v ∈ V, ∃ a ∈ A, a⁻¹ * v ∈ pPrimeCoreOf 2 M) : ∃ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ A := by
  set O := pPrimeCoreOf 2 M with hO
  have hOodd : Odd (Nat.card ↥O) := TwoThin.card_pPrimeCoreOf_odd M
  have hAN : A ≤ normalizer (O : Set G) := fun a ha => mem_normalizer_pPrimeCoreOf (hAM ha)
  have hinf : O ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgO, hgA⟩ := Subgroup.mem_inf.1 hg
    have h1 : orderOf g ∣ Nat.card ↥O := Subgroup.orderOf_dvd_natCard O hgO
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hA2) ⟨g, hgA⟩
    have h2 : orderOf g = 2 ^ k := by rw [← hk, Subgroup.orderOf_mk]
    rw [h2] at h1
    have hk0 : k = 0 := by
      by_contra hk0
      have : 2 ∣ Nat.card ↥O := (dvd_pow_self 2 hk0).trans h1
      exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 this)
    rw [hk0, pow_zero] at h2
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h2)
  have hcard := card_sup_mul_card_inf₀ hAN
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 A (O ⊔ A) :=
    isSylowOf_of_card₀ le_sup_right hA2 (m := Nat.card ↥O) (by rw [hcard, mul_comm])
      (fun h => (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h))
  have hVK : V ≤ O ⊔ A := by
    intro v hv
    obtain ⟨a, ha, hav⟩ := hV v hv
    have : v = a * (a⁻¹ * v) := by group
    rw [this]
    exact (O ⊔ A).mul_mem (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hav)
  obtain ⟨k, hk, hkV⟩ := exists_conj_le_sylow₀ hSyl hVK hV2
  have hkM : k ∈ M := (sup_le (TwoThin.pPrimeCoreOf_le M) hAM) hk
  exact ⟨k, hkM, hkV⟩

theorem centralizer_le_of_conj_le {M A V : Subgroup G} (hU : InU0 M A) (hA8 : Nat.card ↥A = 8)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hVel : CFSG.IsElementaryAbelian 2 ↥V) (hV4 : Nat.card ↥V = 4)
    {m : G} (hm : m ∈ M) (hmV : ∀ v ∈ V, m * v * m⁻¹ ∈ A) : centralizer (V : Set G) ≤ M := by
  set V' := V.map (MulAut.conj m).toMonoidHom with hV'
  have hV'A : V' ≤ A := by
    rintro _ ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply] using hmV v hv
  have hV'el : CFSG.IsElementaryAbelian 2 ↥V' := P151Model.isElementaryAbelian_map (MulAut.conj m) hVel
  have hV'4 : Nat.card ↥V' = 4 := by
    rw [← hV4]
    exact Nat.card_congr ((MulAut.conj m).subgroupMap V).toEquiv.symm
  have hr' : pRank 2 ↥V' = 2 := pRank_eq_of_card_eq_pow one_lt_two (k := 2) (by rw [hV'4]; norm_num)
  have hrA : pRank 2 ↥A = 3 := pRank_eq_of_card_eq_pow one_lt_two (k := 3) (by rw [hA8]; norm_num)
  have hgam := hU.2.2
  rw [hrA] at hgam
  have hN : normalizer (V' : Set G) ≤ M := by
    refine le_trans ?_ hgam
    exact le_iSup₂_of_le V' hV'A (le_iSup_of_le (by rw [hr']) le_rfl)
  have hC : centralizer (V' : Set G) ≤ M := (Subgroup.centralizer_le_normalizer _).trans hN
  intro g hg
  have hg' : m * g * m⁻¹ ∈ centralizer (V' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := (Subgroup.mem_centralizer_iff.1 hg) v hv
    calc m * v * m⁻¹ * (m * g * m⁻¹) = m * (v * g) * m⁻¹ := by group
      _ = m * (g * v) * m⁻¹ := by rw [this]
      _ = m * g * m⁻¹ * (m * v * m⁻¹) := by group
  have := hC hg'
  have e : g = m⁻¹ * (m * g * m⁻¹) * m := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) this) hm

theorem centralizer_le_of_isConj_bar {M : Subgroup G} {x v : G} (hCx : centralizer ({x} : Set G) ≤ M)
    (hxM : x ∈ M) (hx2 : orderOf x = 2) (hvM : v ∈ M) (hv2 : orderOf v = 2)
    (hc : IsConj (QuotientGroup.mk (⟨v, hvM⟩ : ↥M) : Mbar M) (QuotientGroup.mk (⟨x, hxM⟩ : ↥M))) :
    centralizer ({v} : Set G) ≤ M := by
  obtain ⟨m, hm, hmv⟩ := exists_conj_of_isConj_bar hvM hxM hv2 hx2 hc
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hg' : m * g * m⁻¹ ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hmv] at hg
    calc m * g * m⁻¹ * x = m * (g * (m⁻¹ * x * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * x * m) * g) * m⁻¹ := by rw [hg]
      _ = x * (m * g * m⁻¹) := by group
  have := hCx hg'
  have e : g = m⁻¹ * (m * g * m⁻¹) * m := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) this) hm

end Conj

section Exist

variable {G : Type} [Group G] [Finite G]

theorem center_barK_invol {x : G} {K M Q H : Subgroup G} (h1 : Stage2Concl1 x K M Q H)
    (hk1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) (hKq : IsQuasisimple ↥(barIn M K)) :
    ∃ z₀ : Mbar M, ∀ z ∈ barIn M K, (∀ l ∈ barIn M K, z * l = l * z) → z * z = 1 → z = 1 ∨ z = z₀ := by
  classical
  obtain ⟨Z, hZc, hZo, hZn, ⟨e⟩⟩ := T4ElimAssembly.exists_shape_iso h1.K_le hKq
  obtain ⟨zt, -, hztc, -⟩ := (T3S1.s1Facts_of_qShape1 _ hk1).center
  have himg : ∀ w : ↥(barIn M K), (∀ l ∈ barIn M K, (w : Mbar M) * l = l * w) →
      e.symm (QuotientGroup.mk w) = 1 ∨ e.symm (QuotientGroup.mk w) = zt := by
    intro w hw
    refine (hztc _).1 (Subgroup.mem_center_iff.2 fun g => ?_)
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (e g)
    rw [← hu, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hw u u.2).symm
  have hodd : ∀ w : ↥(barIn M K), w ∈ Z → w * w = 1 → w = 1 := by
    intro w hwZ hww
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hww)
    have hdvd' : orderOf w ∣ Nat.card ↥Z := Subgroup.orderOf_dvd_natCard _ hwZ
    have h1' : orderOf w = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hdvd'
        exact absurd (Odd.of_dvd_nat hZo hdvd') (by decide)
    exact orderOf_eq_one_iff.1 h1'
  by_cases hex : ∃ z' ∈ barIn M K, (∀ l ∈ barIn M K, z' * l = l * z') ∧ z' * z' = 1 ∧ z' ≠ 1
  · obtain ⟨z', hz'K, hz'c, hz'z', hz'1⟩ := hex
    refine ⟨z', fun z hz hzc hzz => ?_⟩
    have hz'img : e.symm (QuotientGroup.mk (⟨z', hz'K⟩ : ↥(barIn M K))) = zt := by
      rcases himg ⟨z', hz'K⟩ hz'c with h | h
      · exfalso
        apply hz'1
        have hZ' : (⟨z', hz'K⟩ : ↥(barIn M K)) ∈ Z := by
          have := congrArg e h
          rw [MulEquiv.apply_symm_apply, map_one] at this
          exact (QuotientGroup.eq_one_iff _).1 this
        exact congrArg Subtype.val (hodd _ hZ' (Subtype.ext hz'z'))
      · exact h
    rcases himg ⟨z, hz⟩ hzc with h | h
    · left
      have hZ' : (⟨z, hz⟩ : ↥(barIn M K)) ∈ Z := by
        have := congrArg e h
        rw [MulEquiv.apply_symm_apply, map_one] at this
        exact (QuotientGroup.eq_one_iff _).1 this
      exact congrArg Subtype.val (hodd _ hZ' (Subtype.ext hzz))
    · right
      have heq : (QuotientGroup.mk (⟨z, hz⟩ : ↥(barIn M K)) : ↥(barIn M K) ⧸ Z) =
          QuotientGroup.mk ⟨z', hz'K⟩ := by
        apply e.symm.injective
        rw [h, hz'img]
      have hmem : (⟨z, hz⟩ : ↥(barIn M K))⁻¹ * ⟨z', hz'K⟩ ∈ Z := QuotientGroup.eq.1 heq
      have hcomm : z * z' = z' * z := (hz'c z hz).symm
      have hsq : ((⟨z, hz⟩ : ↥(barIn M K))⁻¹ * ⟨z', hz'K⟩) * ((⟨z, hz⟩ : ↥(barIn M K))⁻¹ * ⟨z', hz'K⟩) = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
        rw [hzi]
        calc z * z' * (z * z') = z * (z' * z) * z' := by group
          _ = z * (z * z') * z' := by rw [hcomm]
          _ = (z * z) * (z' * z') := by group
          _ = 1 := by rw [hzz, hz'z', one_mul]
      have h1' := hodd _ hmem hsq
      have : (⟨z, hz⟩ : ↥(barIn M K)) = ⟨z', hz'K⟩ := by
        rw [inv_mul_eq_one] at h1'
        exact h1'
      exact congrArg Subtype.val this
  · refine ⟨1, fun z hz hzc hzz => Or.inl ?_⟩
    by_contra h
    exact hex ⟨z, hz, hzc, hzz, h⟩

omit [Finite G] in
theorem mem_core_of_mk_eq_one {M : Subgroup G} (m : ↥M) (h : QuotientGroup.mk' (pPrimeCore 2 ↥M) m = 1) :
    (m : G) ∈ pPrimeCoreOf 2 M := by
  have h' := mk_eq_mk_iff.1 (show QuotientGroup.mk' (pPrimeCore 2 ↥M) 1 = QuotientGroup.mk' (pPrimeCore 2 ↥M) m by
    rw [map_one, h])
  simpa using h'

omit [Finite G] in
theorem mem_normalizer_inf_core {M I : Subgroup G} {g : G} (hgI : g ∈ I) (hgM : g ∈ M) :
    g ∈ normalizer ((I ⊓ pPrimeCoreOf 2 M : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · obtain ⟨hnI, hnO⟩ := Subgroup.mem_inf.1 hn
    exact Subgroup.mem_inf.2 ⟨I.mul_mem (I.mul_mem hgI hnI) (I.inv_mem hgI),
      TwoThin.pPrimeCoreOf_normalized M hgM hnO⟩
  · obtain ⟨hnI, hnO⟩ := Subgroup.mem_inf.1 hn
    have e : n = g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ := by group
    rw [e]
    exact Subgroup.mem_inf.2 ⟨I.mul_mem (I.mul_mem (I.inv_mem hgI) hnI) (I.inv_mem (I.inv_mem hgI)),
      TwoThin.pPrimeCoreOf_normalized M (M.inv_mem hgM) hnO⟩

omit [Finite G] in
theorem comm_of_le {M P : Subgroup G} (hPM : P ≤ M) (z : Mbar M)
    (h : P ≤ ((centralizer ({z} : Set (Mbar M))).comap (QuotientGroup.mk' (pPrimeCore 2 ↥M))).map M.subtype) :
    ∀ (p : G) (hp : p ∈ P), QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p, hPM hp⟩ * z =
      z * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨p, hPM hp⟩ := by
  intro p hp
  obtain ⟨m, hm, hmp⟩ := Subgroup.mem_map.1 (h hp)
  have e : (⟨p, hPM hp⟩ : ↥M) = m := Subtype.ext hmp.symm
  rw [e]
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 hm)

omit [Finite G] in
theorem ne_one_of_centralizer_le {M : Subgroup G} (hMtop : M ≠ ⊤) {v : G}
    (hv : centralizer ({v} : Set G) ≤ M) : v ≠ 1 := by
  rintro rfl
  apply hMtop
  rw [eq_top_iff]
  intro g _
  exact hv (Subgroup.mem_centralizer_singleton_iff.2 (by simp))

theorem centralizer_le_of_conj_mk {M : Subgroup G} {x v : G} (hCx : centralizer ({x} : Set G) ≤ M)
    (hxM : x ∈ M) (hx2 : orderOf x = 2) (hvM : v ∈ M) (hvv : v * v = 1) (c : Mbar M)
    (hc : c * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hxM⟩ * c⁻¹ = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨v, hvM⟩) :
    centralizer ({v} : Set G) ≤ M := by
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  have hx1 : (⟨x, hxM⟩ : ↥M) ≠ 1 := by
    intro h
    have : x = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hx2
    omega
  have hxb := B3aG.mk_ne_one_of_sq (g := ⟨x, hxM⟩) (Subtype.ext hxx) hx1
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hxb
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨1, hvM⟩ : ↥M) = 1 := map_one _
    rw [h1] at hc
    calc QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hxM⟩
        = c⁻¹ * (c * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hxM⟩ * c⁻¹) * c := by group
      _ = 1 := by rw [hc]; group
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hvv) hv1
  exact centralizer_le_of_isConj_bar hCx hxM hx2 hvM hv2 (isConj_iff.2 ⟨c, hc⟩).symm

theorem isPCompIn_two_of_even {Y : Type} [Group Y] [Finite Y] {C K : Subgroup Y} (hK : IsCompIn C K)
    (hev : 2 ∣ Nat.card ↥K) : IsPCompIn 2 C K := by
  refine ⟨hK.1, CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
    hK.2 fun hle => ?_⟩
  have h1 : Nat.card ↥(K.subgroupOf C) ∣ Nat.card ↥(pPrimeCore 2 ↥C) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(K.subgroupOf C) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv
  rw [h2] at h1
  have h3 := Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have h4 := Nat.Coprime.eq_one_of_dvd h3 hev
  omega


theorem exists_frame151 (hB : B_B2_g4) {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1 x K M Q H) (h3 : Stage3A x A M H) (hk1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K))
    (hL5 : PuL5 ↥(barIn M H)) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hax : a ≠ x) :
    ∃ s I e₁ e₂, Frame151 M a s I e₁ e₂ ∧ Frame151Type I := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  have hKM : K ≤ M := h1.K_le
  have hKH : K ≤ H := h1.H_min.1
  have hbarKH : barIn M K ≤ barIn M H := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, hKH hm, rfl⟩
  have hHn : (barIn M H).Normal := by
    rw [h3.H_simple.1]
    exact (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hCx : centralizer ({x} : Set G) ≤ M := h3.Cx_le
  have hxM : x ∈ M := hCx hxC
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  set xb : Mbar M := ρ ⟨x, hxM⟩ with hxb
  have hxH : xb ∈ barIn M H := T4S1.mk_mem_barIn hs h3 hL5 hxM hxx
  have hcomp := Prop31.isCompIn_barIn_centralizer hB hs hxM hCx
  have hKq : IsQuasisimple ↥(barIn M K) := Prop31.isQuasisimple_of_isCompIn hcomp
  have hcompH : IsCompIn (barIn M H ⊓ centralizer ({xb} : Set (Mbar M))) (barIn M K) :=
    Prop31.isCompIn_of_le (le_inf hbarKH hcomp.1) inf_le_right hcomp
  obtain ⟨z₀, hz₀⟩ := center_barK_invol h1 hk1 hKq
  have hAK : A ≤ K := T4S1.A_le_K hs hk1
  have hAM : A ≤ M := hAK.trans hKM
  obtain ⟨hAx, hAel, hA8, -⟩ := hs.src
  obtain ⟨hĀE8, hĀH⟩ := T4S1.barA_E8 hs h1 hk1
  have hsqA : ∀ g ∈ A, g * g = 1 := fun g hg => P151Model.ea_sq hAel hg
  have haM : a ∈ M := hAM haA
  have haa : a * a = 1 := hsqA a haA
  have hxa : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.1 (hAx haA)
  set J := barIn M H with hJ
  set t : ↥J := ⟨xb, hxH⟩ with ht
  set L : Subgroup ↥J := (barIn M K).subgroupOf J with hL
  set AJ : Subgroup ↥J := (barIn M A).subgroupOf J with hAJ
  set ab : Mbar M := ρ ⟨a, haM⟩ with hab
  have habA : ab ∈ barIn M A := ⟨⟨a, haM⟩, Subgroup.mem_subgroupOf.2 haA, rfl⟩
  have habH : ab ∈ J := hĀH habA
  set aJ : ↥J := ⟨ab, habH⟩ with haJ
  have htt : t * t = 1 := by
    apply Subtype.ext
    show xb * xb = 1
    rw [hxb, ← map_mul, show (⟨x, hxM⟩ : ↥M) * ⟨x, hxM⟩ = 1 from Subtype.ext hxx, map_one]
  have hx1 : (⟨x, hxM⟩ : ↥M) ≠ 1 := by
    intro h'
    have hx1' : x = 1 := congrArg Subtype.val h'
    rw [hx1', orderOf_one] at hx2
    omega
  have hxb1 : xb ≠ 1 := B3aG.mk_ne_one_of_sq (g := ⟨x, hxM⟩) (Subtype.ext hxx) hx1
  have ht1 : t ≠ 1 := fun h => hxb1 (congrArg Subtype.val h)
  have hLmap : L.map J.subtype = barIn M K := Subgroup.map_subgroupOf_eq_of_le hbarKH
  have hLcomp : IsCompIn (centralizer ({t} : Set ↥J)) L := by
    refine B3aG.isCompIn_of_map_injective J.subtype_injective ?_
    rw [B3aG.map_subtype_centralizer, hLmap]
    exact hcompH
  have hZL : ∃ z₀' : ↥J, ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z * z = 1 → z = 1 ∨ z = z₀' := by
    by_cases hz₀J : z₀ ∈ J
    · refine ⟨⟨z₀, hz₀J⟩, fun z hz hzc hzz => ?_⟩
      have hzK : (z : Mbar M) ∈ barIn M K := Subgroup.mem_subgroupOf.1 hz
      rcases hz₀ (z : Mbar M) hzK (fun l hl => congrArg Subtype.val
        (hzc ⟨l, hbarKH hl⟩ (Subgroup.mem_subgroupOf.2 hl))) (congrArg Subtype.val hzz) with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
    · refine ⟨1, fun z hz hzc hzz => Or.inl ?_⟩
      have hzK : (z : Mbar M) ∈ barIn M K := Subgroup.mem_subgroupOf.1 hz
      rcases hz₀ (z : Mbar M) hzK (fun l hl => congrArg Subtype.val
        (hzc ⟨l, hbarKH hl⟩ (Subgroup.mem_subgroupOf.2 hl))) (congrArg Subtype.val hzz) with h | h
      · exact Subtype.ext h
      · exact absurd (h ▸ z.2) hz₀J
  have hAJL : AJ ≤ L := Subgroup.subgroupOf_mono J (Subgroup.map_mono (Subgroup.subgroupOf_mono M hAK))
  have haJA : aJ ∈ AJ := Subgroup.mem_subgroupOf.2 habA
  have ha1' : (⟨a, haM⟩ : ↥M) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hab1 : ab ≠ 1 := B3aG.mk_ne_one_of_sq (Subtype.ext haa) ha1'
  have haJ1 : aJ ≠ 1 := fun h => hab1 (congrArg Subtype.val h)
  have haJt : aJ ≠ t := by
    intro h
    have h' : ab = xb := congrArg Subtype.val h
    have hax' : (⟨a, haM⟩ : ↥M) * ⟨x, hxM⟩ ≠ 1 := by
      intro h''
      apply hax
      have := congrArg Subtype.val h''
      simp only [Subgroup.coe_mul, Subgroup.coe_one] at this
      calc a = a * x * x := by rw [mul_assoc, hxx, mul_one]
        _ = x := by rw [this, one_mul]
    have hsq : (⟨a, haM⟩ : ↥M) * ⟨x, hxM⟩ * (⟨a, haM⟩ * ⟨x, hxM⟩) = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_one]
      calc a * x * (a * x) = a * (x * a) * x := by group
        _ = a * (a * x) * x := by rw [hxa]
        _ = (a * a) * (x * x) := by group
        _ = 1 := by rw [haa, hxx, one_mul]
    apply B3aG.mk_ne_one_of_sq hsq hax'
    rw [map_mul]
    change ab * xb = 1
    rw [h']
    exact congrArg Subtype.val htt
  obtain ⟨sJ, hsJsJ, hsJaJ, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩, IJ, hIJ, hTJ, hZIJ, e₁J, e₂J, he₁IJ, he₂IJ, he₁J₁, he₂J₂, he₁₂J,
    he₁J1, he₂J1, hneJ, ⟨g₃, hg₃⟩, ⟨g₄, hg₄⟩, ⟨g₅, hg₅⟩, g₆, hg₆₁, hg₆₂⟩ :=
    P151Model.p151Fact_of_puL5 hL5 t L AJ htt ht1 hLcomp hZL hĀE8.1 hĀE8.2 hAJL aJ haJA haJ1 haJt
  have hMtop : M ≠ ⊤ := h1.preuniq.1
  have hPa : zpowers a ≤ M := (Subgroup.zpowers_le).2 haM
  have hzpa : IsPGroup 2 ↥(zpowers a) := by
    have := isElementaryAbelian_zpowers_invol haa
    exact IsElementaryAbelian.isPGroup 2 _
  have hsJa : (sJ : Mbar M) * ab = ab * (sJ : Mbar M) := congrArg Subtype.val hsJaJ
  obtain ⟨s, hsM, hsρ, hss, hsP⟩ := exists_lift_comm hzpa hPa (sJ : Mbar M) (congrArg Subtype.val hsJsJ)
    (comm_of_le hPa _ ((Subgroup.zpowers_le).2
      ⟨⟨a, haM⟩, Subgroup.mem_centralizer_singleton_iff.2 hsJa.symm, rfl⟩))
  have hsa' : s * a = a * s := (hsP a (Subgroup.mem_zpowers a)).symm
  have hCs : centralizer ({s} : Set G) ≤ M :=
    centralizer_le_of_conj_mk hCx hxM hx2 hsM hss (g₁ : Mbar M) (by
      rw [hsρ]
      exact congrArg Subtype.val hg₁)
  have hs1 : s ≠ 1 := ne_one_of_centralizer_le hMtop hCs
  have hasM : a * s ∈ M := M.mul_mem haM hsM
  have hasas : a * s * (a * s) = 1 := by
    calc a * s * (a * s) = a * (s * a) * s := by group
      _ = a * (a * s) * s := by rw [hsa']
      _ = (a * a) * (s * s) := by group
      _ = 1 := by rw [haa, hss, one_mul]
  have hCas : centralizer ({a * s} : Set G) ≤ M :=
    centralizer_le_of_conj_mk hCx hxM hx2 hasM hasas (g₂ : Mbar M) (by
      rw [show (⟨a * s, hasM⟩ : ↥M) = ⟨a, haM⟩ * ⟨s, hsM⟩ from rfl, map_mul, hsρ]
      exact congrArg Subtype.val hg₂)
  set Y : Subgroup G := centralizer ({s} : Set G) ⊓ centralizer ({a} : Set G) with hY
  have hYM : Y ≤ M := inf_le_left.trans hCs
  set φ : ↥Y →* Mbar M := ρ.comp (Subgroup.inclusion hYM) with hφ
  have hker : ¬ 2 ∣ Nat.card φ.ker :=
    B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hYM) (Subgroup.inclusion_injective hYM)
      (pPrimeCore 2 ↥M) (Nat.Coprime.odd_of_left CFSG.pPrimeCore_coprime_card)
  have hrange : φ.range = centralizer ({(sJ : Mbar M)} : Set (Mbar M)) ⊓ centralizer ({ab} : Set (Mbar M)) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨hys, hya⟩ := Subgroup.mem_inf.1 y.2
      have hys' : (y : G) * s = s * y := Subgroup.mem_centralizer_singleton_iff.1 hys
      have hya' : (y : G) * a = a * y := Subgroup.mem_centralizer_singleton_iff.1 hya
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      · rw [← hsρ]
        show ρ ⟨y, hYM y.2⟩ * ρ ⟨s, hsM⟩ = ρ ⟨s, hsM⟩ * ρ ⟨y, hYM y.2⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hys'
      · show ρ ⟨y, hYM y.2⟩ * ρ ⟨a, haM⟩ = ρ ⟨a, haM⟩ * ρ ⟨y, hYM y.2⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hya'
    · intro z hz
      obtain ⟨hzs, hza⟩ := Subgroup.mem_inf.1 hz
      have hzs' : z * sJ = sJ * z := Subgroup.mem_centralizer_singleton_iff.1 hzs
      have hza' : z * ab = ab * z := Subgroup.mem_centralizer_singleton_iff.1 hza
      have hPsa : zpowers s ⊔ zpowers a ≤ M := sup_le ((Subgroup.zpowers_le).2 hsM) hPa
      have hcsa : ∀ h ∈ zpowers s, h * a = a * h := by
        intro h hh
        obtain h' | h' := mem_zpowers_invol hss hh
        · rw [h']; simp
        · rw [h']; exact hsa'
      have hPsa2 : IsPGroup 2 ↥(zpowers s ⊔ zpowers a) := by
        have := B3.S3Sec29H.isElementaryAbelian_sup_zpowers (isElementaryAbelian_zpowers_invol hss) haa hcsa
        exact IsElementaryAbelian.isPGroup 2 _
      obtain ⟨w, hwM, hwz, hwP⟩ := exists_lift_comm' hPsa2 hPsa z (comm_of_le hPsa z (sup_le
        ((Subgroup.zpowers_le).2 ⟨⟨s, hsM⟩, Subgroup.mem_centralizer_singleton_iff.2 (by rw [hsρ]; exact hzs'.symm),
          rfl⟩)
        ((Subgroup.zpowers_le).2 ⟨⟨a, haM⟩, Subgroup.mem_centralizer_singleton_iff.2 hza'.symm, rfl⟩)))
      have hwY : w ∈ Y := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
        (hwP s (Subgroup.mem_sup_left (Subgroup.mem_zpowers s))).symm,
        Subgroup.mem_centralizer_singleton_iff.2 (hwP a (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))).symm⟩
      exact ⟨⟨w, hwY⟩, hwz⟩
  set Jb : Subgroup (Mbar M) := IJ.map J.subtype with hJbdef
  have hJbc : IsCompIn φ.range Jb := by
    have h0 := B3aG.isCompIn_map_of_injective J.subtype_injective hIJ
    rw [Subgroup.map_inf_eq _ _ J.subtype J.subtype_injective, B3aG.map_subtype_centralizer,
      B3aG.map_subtype_centralizer] at h0
    rw [hrange]
    refine LU.Local.isCompIn_of_normal h0 ?_ ?_
    · exact le_inf (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_right)
    · intro c hc y hy
      obtain ⟨hcs, hca⟩ := Subgroup.mem_inf.1 hc
      obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨hyJ, hya⟩ := Subgroup.mem_inf.1 hy₁
      obtain ⟨-, hys⟩ := Subgroup.mem_inf.1 hy₂
      have hcyJ : c * y * c⁻¹ ∈ J := hHn.conj_mem y hyJ c
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hcyJ,
        (centralizer _).mul_mem ((centralizer _).mul_mem hca hya) ((centralizer _).inv_mem hca)⟩,
        Subgroup.mem_inf.2 ⟨hcyJ,
        (centralizer _).mul_mem ((centralizer _).mul_mem hcs hys) ((centralizer _).inv_mem hcs)⟩⟩
  have he₁Jb : (e₁J : Mbar M) ∈ Jb := ⟨e₁J, he₁IJ, rfl⟩
  have he₂Jb : (e₂J : Mbar M) ∈ Jb := ⟨e₂J, he₂IJ, rfl⟩
  have hev : 2 ∣ Nat.card ↥Jb := by
    have ho : orderOf (e₁J : Mbar M) = 2 := by
      have hne : (e₁J : Mbar M) ≠ 1 := fun h => he₁J1 (Subtype.ext h)
      exact orderOf_eq_prime (by rw [sq]; exact congrArg Subtype.val he₁J₁) hne
    have h' := Subgroup.orderOf_dvd_natCard Jb he₁Jb
    rwa [ho] at h'
  have hJb : IsPCompIn 2 φ.range Jb := isPCompIn_two_of_even hJbc hev
  obtain ⟨hIc, hImap⟩ := B1.exists_isPCompIn_lift_of_odd_ker φ hker hJb
  set I : Subgroup G := oPrimeResidualOf 2 ((Jb.comap φ).map Y.subtype) with hIdef
  have hIY : I ≤ Y := hIc.1
  have hIM : I ≤ M := hIY.trans hYM
  have hpre : ∀ u : Mbar M, u ∈ Jb → ∃ g : G, g ∈ I ∧ ∃ hg : g ∈ M, ρ ⟨g, hg⟩ = u := by
    intro u hu
    rw [← hImap] at hu
    obtain ⟨y, hy, hyu⟩ := hu
    exact ⟨y, Subgroup.mem_subgroupOf.1 hy, hYM y.2, hyu⟩
  have hNodd : Odd (Nat.card ↥(I ⊓ pPrimeCoreOf 2 M)) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd M) (Subgroup.card_dvd_of_le inf_le_right)
  have hsqO : ∀ (g : G) (hg : g ∈ M) (u : Mbar M), ρ ⟨g, hg⟩ = u → u * u = 1 → g * g ∈ pPrimeCoreOf 2 M := by
    intro g hg u hgu huu
    exact mem_core_of_mk_eq_one (⟨g, hg⟩ * ⟨g, hg⟩) (by rw [map_mul, hgu, huu])
  obtain ⟨g₁', hg₁'I, hg₁'M, hg₁'ρ⟩ := hpre _ he₁Jb
  obtain ⟨e₁, he₁N, he₁e₁, -⟩ := B3.S3Sec29H.exists_inv_fixed_mem_coset (P := ⊥) (N := I ⊓ pPrimeCoreOf 2 M)
    (g := g₁') IsPGroup.of_bot hNodd bot_le (mem_normalizer_inf_core hg₁'I hg₁'M)
    (Subgroup.mem_inf.2 ⟨I.mul_mem hg₁'I hg₁'I, hsqO _ hg₁'M _ hg₁'ρ (congrArg Subtype.val he₁J₁)⟩)
    (fun p hp => by
      rw [Subgroup.mem_bot.1 hp]
      simp)
  have he₁I : e₁ ∈ I := by
    have e : e₁ = g₁' * (g₁'⁻¹ * e₁) := by group
    rw [e]
    exact I.mul_mem hg₁'I (Subgroup.mem_inf.1 he₁N).1
  have he₁M : e₁ ∈ M := hIM he₁I
  have he₁ρ : ρ ⟨e₁, he₁M⟩ = (e₁J : Mbar M) := by
    rw [← hg₁'ρ]
    exact ((mk_eq_mk_iff (M := M) (m := ⟨g₁', hg₁'M⟩) (m' := ⟨e₁, he₁M⟩)).2 (Subgroup.mem_inf.1 he₁N).2).symm
  have hcommJ : (e₁J : Mbar M) * e₂J = e₂J * e₁J := congrArg Subtype.val he₁₂J
  have hz1 : IsPGroup 2 ↥(zpowers e₁) := by
    have := isElementaryAbelian_zpowers_invol he₁e₁
    exact IsElementaryAbelian.isPGroup 2 _
  obtain ⟨g₂', hg₂'I, hg₂'M, hg₂'ρ⟩ := hpre _ he₂Jb
  obtain ⟨e₂, he₂N, he₂e₂, he₂P⟩ := B3.S3Sec29H.exists_inv_fixed_mem_coset (P := zpowers e₁)
    (N := I ⊓ pPrimeCoreOf 2 M) (g := g₂') hz1 hNodd ((Subgroup.zpowers_le).2 (mem_normalizer_inf_core he₁I he₁M))
    (mem_normalizer_inf_core hg₂'I hg₂'M)
    (Subgroup.mem_inf.2 ⟨I.mul_mem hg₂'I hg₂'I, hsqO _ hg₂'M _ hg₂'ρ (congrArg Subtype.val he₂J₂)⟩)
    (fun p hp => by
      obtain hp' | hp' := mem_zpowers_invol he₁e₁ hp
      · rw [hp']; simp
      · rw [hp']
        refine Subgroup.mem_inf.2 ⟨I.mul_mem (I.inv_mem hg₂'I) (I.mul_mem (I.mul_mem he₁I hg₂'I) (I.inv_mem he₁I)),
          ?_⟩
        exact mem_core_of_mk_eq_one ((⟨g₂', hg₂'M⟩ : ↥M)⁻¹ * (⟨e₁, he₁M⟩ * ⟨g₂', hg₂'M⟩ * (⟨e₁, he₁M⟩ : ↥M)⁻¹))
          (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg₂'ρ, he₁ρ, hcommJ]; group))
  have he₂I : e₂ ∈ I := by
    have e : e₂ = g₂' * (g₂'⁻¹ * e₂) := by group
    rw [e]
    exact I.mul_mem hg₂'I (Subgroup.mem_inf.1 he₂N).1
  have he₂M : e₂ ∈ M := hIM he₂I
  have he₂ρ : ρ ⟨e₂, he₂M⟩ = (e₂J : Mbar M) := by
    rw [← hg₂'ρ]
    exact ((mk_eq_mk_iff (M := M) (m := ⟨g₂', hg₂'M⟩) (m' := ⟨e₂, he₂M⟩)).2 (Subgroup.mem_inf.1 he₂N).2).symm
  have he₁e₂ : e₁ * e₂ = e₂ * e₁ := he₂P e₁ (Subgroup.mem_zpowers e₁)
  have he₁1 : e₁ ≠ 1 := by
    intro h
    apply he₁J1
    apply Subtype.ext
    rw [← he₁ρ, show (⟨e₁, he₁M⟩ : ↥M) = 1 from Subtype.ext h, map_one]
    rfl
  have he₂1 : e₂ ≠ 1 := by
    intro h
    apply he₂J1
    apply Subtype.ext
    rw [← he₂ρ, show (⟨e₂, he₂M⟩ : ↥M) = 1 from Subtype.ext h, map_one]
    rfl
  have hne₁₂ : e₁ ≠ e₂ := by
    intro h
    apply hneJ
    apply Subtype.ext
    rw [← he₁ρ, ← he₂ρ]
    congr 1
    exact Subtype.ext h
  have hIa : ∀ e ∈ I, e * a = a * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hIY he)).2
  have hae : ∀ e, e ∈ I → e * e = 1 → a * e * (a * e) = 1 := by
    intro e he hee
    have hea := hIa e he
    calc a * e * (a * e) = a * (e * a) * e := by group
      _ = a * (a * e) * e := by rw [hea]
      _ = (a * a) * (e * e) := by group
      _ = 1 := by rw [haa, hee, one_mul]
  have hCe₁ : centralizer ({a * e₁} : Set G) ≤ M :=
    centralizer_le_of_conj_mk hCx hxM hx2 (M.mul_mem haM he₁M) (hae e₁ he₁I he₁e₁) (g₃ : Mbar M) (by
      rw [show (⟨a * e₁, M.mul_mem haM he₁M⟩ : ↥M) = ⟨a, haM⟩ * ⟨e₁, he₁M⟩ from rfl, map_mul, he₁ρ]
      exact congrArg Subtype.val hg₃)
  have hCe₂ : centralizer ({a * e₂} : Set G) ≤ M :=
    centralizer_le_of_conj_mk hCx hxM hx2 (M.mul_mem haM he₂M) (hae e₂ he₂I he₂e₂) (g₄ : Mbar M) (by
      rw [show (⟨a * e₂, M.mul_mem haM he₂M⟩ : ↥M) = ⟨a, haM⟩ * ⟨e₂, he₂M⟩ from rfl, map_mul, he₂ρ]
      exact congrArg Subtype.val hg₄)
  have he₁₂sq : e₁ * e₂ * (e₁ * e₂) = 1 := by
    calc e₁ * e₂ * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by group
      _ = e₁ * (e₁ * e₂) * e₂ := by rw [he₁e₂]
      _ = (e₁ * e₁) * (e₂ * e₂) := by group
      _ = 1 := by rw [he₁e₁, he₂e₂, one_mul]
  have hCe₁₂ : centralizer ({a * (e₁ * e₂)} : Set G) ≤ M :=
    centralizer_le_of_conj_mk hCx hxM hx2 (M.mul_mem haM (M.mul_mem he₁M he₂M))
      (hae _ (I.mul_mem he₁I he₂I) he₁₂sq) (g₅ : Mbar M) (by
      rw [show (⟨a * (e₁ * e₂), M.mul_mem haM (M.mul_mem he₁M he₂M)⟩ : ↥M) =
        ⟨a, haM⟩ * (⟨e₁, he₁M⟩ * ⟨e₂, he₂M⟩) from rfl, map_mul, map_mul, he₁ρ, he₂ρ]
      exact congrArg Subtype.val hg₅)
  set V : Subgroup G := zpowers e₁ ⊔ zpowers e₂ with hVdef
  have hc₁₂ : ∀ h ∈ zpowers e₁, h * e₂ = e₂ * h := by
    intro h hh
    obtain h' | h' := mem_zpowers_invol he₁e₁ hh
    · rw [h']; simp
    · rw [h']; exact he₁e₂
  have hVel : CFSG.IsElementaryAbelian 2 ↥V :=
    B3.S3Sec29H.isElementaryAbelian_sup_zpowers (isElementaryAbelian_zpowers_invol he₁e₁) he₂e₂ hc₁₂
  have hV4 : Nat.card ↥V = 4 := card_four he₁e₁ he₂e₂ he₁e₂ he₁1 he₂1 hne₁₂
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) (g₆ : Mbar M)
  set W : Subgroup G := ((barIn M A).comap ρ).map M.subtype with hW
  have hconjW : ∀ (e : G) (he : e ∈ M) (eJ : ↥J), ρ ⟨e, he⟩ = (eJ : Mbar M) → g₆ * eJ * g₆⁻¹ ∈ AJ →
      (m₀ : G) * e * (m₀ : G)⁻¹ ∈ W := by
    intro e he eJ heρ hmem
    refine ⟨m₀ * ⟨e, he⟩ * m₀⁻¹, ?_, rfl⟩
    show ρ (m₀ * ⟨e, he⟩ * m₀⁻¹) ∈ barIn M A
    rw [map_mul, map_mul, map_inv, hm₀, heρ]
    exact Subgroup.mem_subgroupOf.1 hmem
  set V' : Subgroup G := V.map (MulAut.conj (m₀ : G)).toMonoidHom with hV'
  have hV'W : V' ≤ W := by
    rw [hV', hVdef, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
    · exact hconjW e₁ he₁M e₁J he₁ρ hg₆₁
    · exact hconjW e₂ he₂M e₂J he₂ρ hg₆₂
  have hV'A : ∀ v ∈ V', ∃ a' ∈ A, a'⁻¹ * v ∈ pPrimeCoreOf 2 M := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hV'W hv
    obtain ⟨a'', ha'', ha''w⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hw)
    exact ⟨a'', Subgroup.mem_subgroupOf.1 ha'', mk_eq_mk_iff.1 ha''w⟩
  have hA2 : IsPGroup 2 ↥A := by
    have := hAel
    exact IsElementaryAbelian.isPGroup 2 _
  have hV'2 : IsPGroup 2 ↥V' := by
    have := P151Model.isElementaryAbelian_map (MulAut.conj (m₀ : G)) hVel
    exact IsElementaryAbelian.isPGroup 2 _
  obtain ⟨m₁, hm₁M, hm₁⟩ := exists_conj_into hAM hA2 hV'2 hV'A
  have hCE : centralizer (V : Set G) ≤ M := by
    refine centralizer_le_of_conj_le (inU0_A hs) hA8 hAel hVel hV4 (m := m₁ * (m₀ : G)) (M.mul_mem hm₁M m₀.2) ?_
    intro v hv
    have h' := hm₁ _ ⟨v, hv, rfl⟩
    have e : m₁ * (m₀ : G) * v * (m₁ * (m₀ : G))⁻¹ = m₁ * ((m₀ : G) * v * (m₀ : G)⁻¹) * m₁⁻¹ := by group
    rw [e]
    exact h'
  have hfI : ∀ i : ↥I, φ (Subgroup.inclusion hIY i) ∈ Jb := by
    intro i
    rw [← hImap]
    exact ⟨Subgroup.inclusion hIY i, Subgroup.mem_subgroupOf.2 i.2, rfl⟩
  set fI : ↥I →* ↥Jb := (φ.comp (Subgroup.inclusion hIY)).codRestrict Jb hfI with hfIdef
  have hfIs : Function.Surjective fI := by
    rintro ⟨y, hy⟩
    rw [← hImap] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨⟨w, Subgroup.mem_subgroupOf.1 hw⟩, rfl⟩
  have hfIodd : Odd (Nat.card fI.ker) := by
    have hk : fI.ker = φ.ker.comap (Subgroup.inclusion hIY) := by
      rw [hfIdef, MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]
    rw [hk]
    have hodd : Odd (Nat.card φ.ker) := Nat.odd_iff.2 (by omega)
    exact Odd.of_dvd_nat hodd (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hIY))
  have hJbq : IsQuasisimple ↥Jb := Prop31.isQuasisimple_of_isCompIn hJbc
  set eJ : ↥IJ ≃* ↥Jb := IJ.equivMapOfInjective J.subtype J.subtype_injective with heJ
  have hJbT : IsL3OddSD (↥Jb ⧸ center ↥Jb) :=
    P151Model.isL3OddSD_equiv (CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr eJ) hTJ
  have hJbZ : ∀ z : ↥Jb, z ∈ center ↥Jb → z * z = 1 → z = 1 := by
    intro z hz hzz
    set w := eJ.symm z with hw
    have hwc : ∀ l ∈ IJ, (w : ↥J) * l = l * w := by
      intro l hl
      have h1 := Subgroup.mem_center_iff.1 hz (eJ ⟨l, hl⟩)
      have h2 : eJ ⟨l, hl⟩ * eJ w = eJ w * eJ ⟨l, hl⟩ := by
        rw [hw, MulEquiv.apply_symm_apply]
        exact h1
      rw [← map_mul, ← map_mul] at h2
      exact (congrArg Subtype.val (eJ.injective h2)).symm
    have hww : (w : ↥J) * w = 1 := by
      have : w * w = 1 := by
        apply eJ.injective
        rw [map_mul, hw, MulEquiv.apply_symm_apply, hzz, map_one]
      exact congrArg Subtype.val this
    have hw1 : w = 1 := Subtype.ext (hZIJ (w : ↥J) w.2 hwc hww)
    rw [← MulEquiv.apply_symm_apply eJ z, ← hw, hw1, map_one]
  exact ⟨s, I, e₁, e₂, {
    aM := haM, aa := haa, a1 := ha1, sM := hsM, ss := hss, s1 := hs1, sa := hsa', Cs := hCs, Cas := hCas,
    Icomp := hIc, e₁I := he₁I, e₂I := he₂I, e₁e₁ := he₁e₁, e₂e₂ := he₂e₂, e₁e₂ := he₁e₂, e₁1 := he₁1,
    e₂1 := he₂1, e₁₂ := hne₁₂, Ce₁ := hCe₁, Ce₂ := hCe₂, Ce₁₂ := hCe₁₂, CE := hCE },
    ⟨↥Jb, inferInstance, inferInstance, fI, hfIs, hfIodd, hJbq, hJbT, hJbZ⟩⟩

end Exist

section Leaf

@[expose] def Layer151F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
    Stage2Concl1 x K M Q H → Stage3A x A M H → QShape1 (↥K ⧸ pPrimeCore 2 ↥K) → PuL5 ↥(barIn M H) →
    ∀ (a s : G) (I : Subgroup G) (e₁ e₂ : G), a ∈ A → a ≠ x → Frame151 M a s I e₁ e₂ →
      pLayerOf 2 (centralizer ({a} : Set G)) ≤ M


theorem s1Prop151_of_layer (hB : B_B2_g4) (h2C : Stage2Thm2C) (hL : Layer151F) : T4S1.S1Prop151 := by
  intro G _ _ x K A M P Q H hs h1 h3 hk1 hL5 a haA ha1
  by_cases hax : a = x
  · rw [hax]
    exact h3.Cx_le
  · obtain ⟨s, I, e₁, e₂, hF, -⟩ := exists_frame151 hB hs h1 h3 hk1 hL5 haA ha1 hax
    obtain ⟨-, hAel, -, -⟩ := hs.src
    have hAC : A ≤ centralizer ({a} : Set G) := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.2 (P151Model.ea_comm hAel hb haA)
    exact centralizer_le_of_frame hF h1.preuniq.1 (h2C G x K A M P Q H hs (Stage2Concl1.toCore h1))
      (pPrimeCoreOf_le_of_inU0 (inU0_A hs) hAC) (hL G x K A M P Q H hs h1 h3 hk1 hL5 a s I e₁ e₂ haA hax hF)

end Leaf

end CFSG.GH74.Generic.BProg.B2.T4.P151G
