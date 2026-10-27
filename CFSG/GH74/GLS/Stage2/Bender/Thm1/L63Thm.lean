module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Setup
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Axb
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
public import CFSG.GH74.GLS.Stage2.Signalizer.L199
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.L64

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section Cases

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M N A B : Subgroup G} {p r : ℕ}

theorem op_le_of_ne (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsr : s ≠ r) : Op s N ≤ M := by
  have h1 := (signalizer_sub L199.ig_19_9 ctx.orderOf_z (sig4Sub ctx h)).1 s hs hs2 hsr
  exact (Subgroup.le_centralizer_iff.mp h1).trans (centralizer_P1_le h)

theorem op_r_le (h : Hyp62 z M N A B r) : Op r N ≤ M := by
  have hr := h.prime
  have : Fact r.Prime := ⟨hr⟩
  have hRp : IsPGroup r ↥(Op r N) := isPGroup_Op r hr N
  have hAp : IsPGroup r ↥A := (isPGroup_Op r hr M).to_le h.A_le_Or
  have hBcop : Nat.Coprime r (Nat.card ↥B) :=
    (coprime_card_Ep hr).coprime_dvd_right (Subgroup.card_dvd_of_le h.B_le_E)
  have hOE : Op r M ≤ centralizer ((Ep r M : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commute_Op_Ep r hr M)
  have hcomm : ∀ a ∈ B, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hOE (h.A_le_Or hb)) a (h.B_le_E ha)
  have hdisj : Disjoint (Ep r M) (Op r N) := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hn]
    exact ((coprime_card_Ep hr).pow_left n).symm
  have key : B ≤ centralizer ((Op r N ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxM : x ∈ M := h.A_mem.2.2.2 (Subgroup.centralizer_le_normalizer _ hx.2)
    have hbE : b ∈ Ep r M := h.B_le_E hb
    have hbN : b ∈ N := h.B_le hb
    have hc1 : x * b * x⁻¹ * b⁻¹ ∈ Ep r M :=
      (Ep r M).mul_mem ((mem_normalizer_iff.mp (le_normalizer_Ep r M hxM) b).mp hbE)
        ((Ep r M).inv_mem hbE)
    have hc2 : x * b * x⁻¹ * b⁻¹ ∈ Op r N := by
      have : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [this]
      exact (Op r N).mul_mem hx.1
        ((mem_normalizer_iff.mp (le_normalizer_Op r N hbN) x⁻¹).mp ((Op r N).inv_mem hx.1))
    have h1 : x * b * x⁻¹ * b⁻¹ = 1 := by
      have := hdisj.le_bot ⟨hc1, hc2⟩
      simpa using this
    have h2 : x * b * x⁻¹ = b := mul_inv_eq_one.mp h1
    calc x * b = (x * b * x⁻¹) * x := by group
      _ = b * x := by rw [h2]
  have hB := ig_11_7_thm G r hr B A (Op r N) hRp hAp hBcop
    (h.B_le.trans (le_normalizer_Op r N)) (h.A_le.trans (le_normalizer_Op r N)) hcomm key
  exact (Subgroup.le_centralizer_iff.mp hB).trans
    ((Subgroup.centralizer_le_normalizer _).trans h.B_mem.2.2.2)


theorem op_two_le (h41c : Prop4_1c) (ctx : Ctx6 G z k S M p) (h : Hyp62 z M N A B r) :
    Op 2 N ≤ M := by
  by_contra hnot
  have hr := h.prime
  have hr2 : r ≠ 2 := r_ne_two ctx h
  have hzN : z ∈ N := h.z_mem
  have hPN : P1 z M N r ≤ N := P1_le_N hzN
  have hPp : IsPGroup r ↥(P1 z M N r) := isPGroup_P1 ctx h
  have hR2 : IsPGroup 2 ↥(Op 2 N) := isPGroup_Op 2 Nat.prime_two N
  have hPcen : ¬ P1 z M N r ≤ centralizer ((Op 2 N : Subgroup G) : Set G) := fun hc =>
    hnot ((Subgroup.le_centralizer_iff.mp hc).trans (centralizer_P1_le h))
  have hd : Disjoint (Op 2 N) (Op r N) :=
    disjoint_of_isPGroup_of_ne Nat.prime_two hr (Ne.symm hr2) hR2 (isPGroup_Op r hr N)
  have hnotP : ¬ P1 z M N r ≤ Op r N := by
    intro hle
    apply hPcen
    have h1 : ⁅Op 2 N, P1 z M N r⁆ ≤ Op 2 N :=
      commutator_le_left_of_le_normalizer (hPN.trans (le_normalizer_Op 2 N))
    have h2 : ⁅Op 2 N, P1 z M N r⁆ ≤ Op r N :=
      (Subgroup.commutator_mono le_rfl hle).trans
        (commutator_le_right_of_le_normalizer ((Op_le 2 N).trans (le_normalizer_Op r N)))
    have h3 : ⁅Op 2 N, P1 z M N r⁆ = ⊥ := le_bot_iff.mp ((le_inf h1 h2).trans hd.le_bot)
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
  set Q : Subgroup ↥N := pCore r ↥N with hQ
  set R' : Subgroup ↥N := pCore 2 ↥N with hR'
  set P' : Subgroup ↥N := (P1 z M N r).subgroupOf N with hP'
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  have hQR : Disjoint Q R' :=
    disjoint_of_isPGroup_of_ne hr Nat.prime_two hr2 pCore_isPGroup pCore_isPGroup
  have hRR' : Op 2 N = R'.map N.subtype := rfl
  have hPP' : P'.map N.subtype = P1 z M N r := Subgroup.map_subgroupOf_eq_of_le hPN
  have hcommR : ⁅Op 2 N, P1 z M N r⁆ = (⁅R', P'⁆).map N.subtype := by
    rw [Subgroup.map_commutator, hPP', ← hRR']
  have hsig := sig4B_of_sub ctx.orderOf_z (sig4Sub ctx h) hnotP
  set W : Subgroup (Sec N (pCore r ↥N)) := R'.map (QuotientGroup.mk' Q) with hW
  have hWnorm : W.Normal :=
    Subgroup.Normal.map (inferInstance : R'.Normal) (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  have hNW : ∀ g : Sec N (pCore r ↥N), g ∈ normalizer (W : Set (Sec N (pCore r ↥N))) := fun g =>
    Subgroup.normalizer_eq_top_iff.mpr hWnorm ▸ Subgroup.mem_top g
  have hW2 : IsPGroup 2 ↥W := pCore_isPGroup.map (QuotientGroup.mk' Q)
  have hne : ⁅W, xBar r N (P1 z M N r)⁆ ≠ ⊥ := by
    intro hbot
    have h1 : ⁅W, xBar r N (P1 z M N r)⁆ = (⁅R', P'⁆).map (QuotientGroup.mk' Q) := by
      rw [Subgroup.map_commutator]
      rfl
    rw [h1, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have h2 : ⁅R', P'⁆ ≤ R' := Subgroup.commutator_le_left R' P'
    have h3 : ⁅R', P'⁆ = ⊥ := le_bot_iff.mp ((le_inf hbot h2).trans hQR.le_bot)
    apply hPcen
    have h4 : ⁅Op 2 N, P1 z M N r⁆ = ⊥ := by rw [hcommR, h3, Subgroup.map_bot]
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h4)
  obtain ⟨-, hrel, halt⟩ := h41c G z k S ctx.ctx N Q hzN r (xBar r N (P1 z M N r)) hsig W hW2
    (fun g _ => hNW g) (hNW _) hne
  have halt' : oddPart (AutOrd ⊤ ⁅W, xBar r N (P1 z M N r)⁆) ∣ 9 ∨
      NormIso ⁅W, xBar r N (P1 z M N r)⁆ (Equiv.Perm (Fin 4)) :=
    halt.imp (fun h => h.2.2.2) (fun h => h.2.2)
  have hXp : IsPGroup r ↥(xBar r N (P1 z M N r)) :=
    (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm).map (QuotientGroup.mk' Q)
  have hr3 : r = 3 := by
    have h1 : (centralizer (W : Set (Sec N (pCore r ↥N)))).relIndex (xBar r N (P1 z M N r)) ∣
        Nat.card ↥(xBar r N (P1 z M N r)) := Subgroup.index_dvd_card _
    rw [hrel] at h1
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hXp
    rw [hn] at h1
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
      (Nat.prime_three.dvd_of_dvd_pow h1)).symm
  set Bbar : Subgroup (Sec N (pCore r ↥N)) := B'.map (QuotientGroup.mk' Q) with hBbar
  have hBcardB' : Nat.card ↥B' = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.B_le).toEquiv
  have hBbar_dvd : Nat.card ↥Bbar ∣ Nat.card ↥B :=
    hBcardB' ▸ Subgroup.card_map_dvd B' (QuotientGroup.mk' Q)
  have hBodd : Odd (Nat.card ↥B) :=
    Odd.of_dvd_nat (odd_card_E1 ctx) (Subgroup.card_dvd_of_le (B_le_E1 h))
  have hBbar_odd : Odd (Nat.card ↥Bbar) := Odd.of_dvd_nat hBodd hBbar_dvd
  have hBcop : Nat.Coprime r (Nat.card ↥B) :=
    (coprime_card_E1 h).coprime_dvd_right (Subgroup.card_dvd_of_le (B_le_E1 h))
  have hBbar3 : Nat.Coprime 3 (Nat.card ↥Bbar) := hr3 ▸ hBcop.coprime_dvd_right hBbar_dvd
  have hBcX : Bbar ≤ centralizer ((xBar r N (P1 z M N r) : Subgroup (Sec N (pCore r ↥N))) :
      Set (Sec N (pCore r ↥N))) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hbG : (b : G) ∈ B := hb
    have hxG : (x : G) ∈ P1 z M N r := hx
    have hc : (x : G) * (b : G) = (b : G) * (x : G) :=
      Subgroup.mem_centralizer_iff.mp ((E1_le_centralizer_P1 ctx h) (B_le_E1 h hbG)) (x : G) hxG
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hc)
  have hBN : Bbar ≤ normalizer ((⁅W, xBar r N (P1 z M N r)⁆ : Subgroup (Sec N (pCore r ↥N))) :
      Set (Sec N (pCore r ↥N))) :=
    le_normalizer_commutator (fun g _ => hNW g) (hBcX.trans (Subgroup.centralizer_le_normalizer _))
  have hBc := le_centralizer_of_coprime_relIndex hBN (coprime_relIndex_of_alt hBbar_odd hBbar3 halt')
  have hB'c : B' ≤ centralizer ((⁅R', P'⁆ : Subgroup ↥N) : Set ↥N) :=
    le_centralizer_commutator_of_map hQR hBc
  have hBcP : B ≤ centralizer ((⁅Op 2 N, P1 z M N r⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [hcommR] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have hbN : b ∈ N := h.B_le hb
    have := Subgroup.mem_centralizer_iff.mp (hB'c (show (⟨b, hbN⟩ : ↥N) ∈ B' from hb)) w' hw'
    exact congrArg Subtype.val this
  have hKM : ⁅Op 2 N, P1 z M N r⁆ ≤ M :=
    (Subgroup.le_centralizer_iff.mp hBcP).trans
      ((Subgroup.centralizer_le_normalizer _).trans h.B_mem.2.2.2)
  have hRn : ¬ r ∣ Nat.card ↥(Op 2 N) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hR2
    rw [hn]
    intro hdv
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdv))
  have hdec := le_commutator_sup_inf_centralizer hr hPp (hPN.trans (le_normalizer_Op 2 N)) hRn
  exact hnot (hdec.trans (sup_le hKM (inf_le_right.trans (centralizer_P1_le h))))

end Cases

theorem lemma6_3_thm (h41c : Prop4_1c) : Lemma6_3 := by
  intro G _ _ z k S M p ctx N A B r h
  rw [Fm_def, CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore (G := ↥N), Subgroup.map_iSup]
  refine iSup_le fun s => ?_
  have hsp : (s : ℕ).Prime := Nat.prime_of_mem_primeFactors s.2
  show Op (s : ℕ) N ≤ M
  by_cases hsr : (s : ℕ) = r
  · rw [hsr]
    exact op_r_le h
  · by_cases hs2 : (s : ℕ) = 2
    · rw [hs2]
      exact op_two_le h41c ctx h
    · exact op_le_of_ne ctx h hsp hs2 hsr

end CFSG.GH74.GLS.Stage2.Bender.Thm1.L64
