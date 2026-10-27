module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0b
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

section CentreLemma

theorem yLifts_inf_centralizer_le_pCore_aux1 {H ι : Type} [Group H] (f : ι → Subgroup H)
    (s : Finset ι)
    (hz : ∀ i ∈ s, ∀ a ∈ f i, (∀ b ∈ f i, a * b = b * a) → a = 1)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, a * b = b * a) {z : H}
    (hzs : z ∈ ⨆ i ∈ s, f i) (hzc : ∀ i ∈ s, ∀ a ∈ f i, z * a = a * z) : z = 1 := by
  classical
  induction s using Finset.induction_on generalizing z with
  | empty =>
    simpa using hzs
  | insert j s hj ih =>
    rw [Finset.iSup_insert] at hzs
    have hS : (⨆ i ∈ s, f i) ≤ Subgroup.centralizer (f j : Set H) := by
      refine iSup₂_le fun i hi => ?_
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hc j (Finset.mem_insert_self j s) i (Finset.mem_insert_of_mem hi)
        (fun h => hj (h ▸ hi)) b hb a ha)
    have hN : (⨆ i ∈ s, f i) ≤ Subgroup.normalizer (f j : Set H) :=
      hS.trans (Subgroup.centralizer_le_normalizer _)
    have hmem : z ∈ ((f j ⊔ ⨆ i ∈ s, f i : Subgroup H) : Set H) := hzs
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at hmem
    obtain ⟨b, hb, t, ht, rfl⟩ := hmem
    have htc : ∀ c ∈ f j, t * c = c * t := fun c hc' =>
      (Subgroup.mem_centralizer_iff.1 (hS ht) c hc').symm
    have hb1 : b = 1 := by
      refine hz j (Finset.mem_insert_self j s) b hb fun c hc' => ?_
      have h2 : b * t * c = c * (b * t) := hzc j (Finset.mem_insert_self j s) c hc'
      have h3 : (b * c) * t = (c * b) * t := by
        calc (b * c) * t = b * (c * t) := by rw [mul_assoc]
          _ = b * (t * c) := by rw [htc c hc']
          _ = b * t * c := by rw [mul_assoc]
          _ = c * (b * t) := h2
          _ = c * b * t := by rw [mul_assoc]
      exact mul_right_cancel h3
    subst hb1
    have ht1 : t = 1 := ih (fun i hi => hz i (Finset.mem_insert_of_mem hi))
      (fun i hi i' hi' hne => hc i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi')
        hne) ht (fun i hi a ha => by simpa using hzc i (Finset.mem_insert_of_mem hi) a ha)
    simp [ht1]

end CentreLemma

section Dichotomy

theorem yLifts_inf_centralizer_le_pCore_aux2 {H : Type} [Group H] {A B : Subgroup H}
    (hA : CFSG.Open.IsQuasisimple ↥A) (hZ : Nat.card (Subgroup.center ↥A) = 1)
    (hn : A ≤ Subgroup.normalizer (B : Set H)) (hAB : ¬ A ≤ B) : A ⊓ B = ⊥ := by
  have hnorm : ((A ⊓ B).subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    rintro n g ⟨hnA, hnB⟩ hgA
    exact ⟨A.mul_mem (A.mul_mem hgA hnA) (A.inv_mem hgA),
      (Subgroup.mem_normalizer_iff.1 (hn hgA) n).1 hnB⟩
  rcases liftOf_central_ext_aux1 hA hnorm with hcen | htop
  · rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A := hx
    have h1 := hcen hx'
    rw [Subgroup.eq_bot_of_card_eq _ hZ, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  · exfalso
    apply hAB
    intro a ha
    have h1 : (⟨a, ha⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A := by
      rw [htop]
      exact Subgroup.mem_top _
    exact h1.2

end Dichotomy

section OddAction

variable {X : Type} [Group X]

theorem yLifts_inf_centralizer_le_pCore_aux3 {S : Subgroup X} {x z : X}
    (hx : ∀ s ∈ S, x * s * x⁻¹ ∈ S) (h : ∀ s ∈ S, x * s * x⁻¹ = z * s * z⁻¹) (n : ℕ) :
    ∀ s ∈ S, x ^ n * s * (x ^ n)⁻¹ = z ^ n * s * (z ^ n)⁻¹ := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
    intro s hs
    have h1 := ih (x * s * x⁻¹) (hx s hs)
    calc x ^ (n + 1) * s * (x ^ (n + 1))⁻¹ = x ^ n * (x * s * x⁻¹) * (x ^ n)⁻¹ := by
          simp only [pow_succ, mul_inv_rev, mul_assoc]
      _ = z ^ n * (x * s * x⁻¹) * (z ^ n)⁻¹ := h1
      _ = z ^ n * (z * s * z⁻¹) * (z ^ n)⁻¹ := by rw [h s hs]
      _ = z ^ (n + 1) * s * (z ^ (n + 1))⁻¹ := by
          simp only [pow_succ, mul_inv_rev, mul_assoc]

theorem yLifts_inf_centralizer_le_pCore_aux4 {S : Subgroup X} {x z : X}
    (hx : ∀ s ∈ S, x * s * x⁻¹ ∈ S) (h : ∀ s ∈ S, x * s * x⁻¹ = z * s * z⁻¹)
    (hodd : Odd (orderOf x)) (hz : ∃ m : ℕ, z ^ (2 ^ m) = 1) :
    ∀ s ∈ S, x * s * x⁻¹ = s := by
  obtain ⟨m, hm⟩ := hz
  have h1 := yLifts_inf_centralizer_le_pCore_aux3 hx h (2 ^ m)
  have hc : x ^ (2 ^ m) ∈ Subgroup.centralizer (S : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h2 := h1 s hs
    rw [hm] at h2
    simp only [inv_one, mul_one, one_mul] at h2
    calc s * x ^ (2 ^ m) = (x ^ (2 ^ m) * s * (x ^ (2 ^ m))⁻¹) * x ^ (2 ^ m) := by
          rw [h2]
      _ = x ^ (2 ^ m) * s := by group
  have hcop : Nat.Coprime (2 ^ m) (orderOf x) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  have hxc : x ∈ Subgroup.centralizer (S : Set X) := by
    rw [← ht]
    exact Subgroup.pow_mem _ hc t
  intro s hs
  have h3 := Subgroup.mem_centralizer_iff.1 hxc s hs
  calc x * s * x⁻¹ = (x * s) * x⁻¹ := rfl
    _ = (s * x) * x⁻¹ := by rw [← h3]
    _ = s := by group

end OddAction

section SquareLemma

variable {X : Type} [Group X]

theorem yLifts_inf_centralizer_le_pCore_aux5 {V : Subgroup X} [hVn : V.Normal]
    (hV : IsElemAbelian 2 V) {x : X} (h : ∀ v ∈ V, x * ⁅x, v⁆ * x⁻¹ = ⁅x, v⁆) :
    ∀ v ∈ V, x ^ 2 * v * (x ^ 2)⁻¹ = v := by
  intro v hv
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    pRank_add_le_pRank_sup_aux_comm hV ha hb
  have hsq : ∀ a ∈ V, a * a = 1 := fun a ha => by simpa [pow_two] using hV.2 a ha
  obtain ⟨a, ha⟩ : ∃ a, a = x * v * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = x * (x * v * x⁻¹) * x⁻¹ := ⟨_, rfl⟩
  have haV : a ∈ V := ha ▸ hVn.conj_mem v hv x
  have h1 := h v hv
  have e1 : x * ⁅x, v⁆ * x⁻¹ = b * a⁻¹ := by
    rw [hb, ha]
    simp only [commutatorElement_def]
    group
  have e2 : ⁅x, v⁆ = a * v⁻¹ := by
    rw [ha]
    simp only [commutatorElement_def]
  rw [e1, e2] at h1
  have h2 : b = a * v⁻¹ * a := by
    calc b = b * a⁻¹ * a := by group
      _ = a * v⁻¹ * a := by rw [h1]
  have hav : a * v⁻¹ = v⁻¹ * a := hcomm a haV v⁻¹ (V.inv_mem hv)
  have h3 : a * v⁻¹ * a = v⁻¹ := by rw [hav, mul_assoc, hsq a haV, mul_one]
  have hvv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v hv)
  calc x ^ 2 * v * (x ^ 2)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by
        simp only [pow_two, mul_inv_rev, mul_assoc]
    _ = b := hb.symm
    _ = v := by rw [h2, h3, hvv]

end SquareLemma

section StepOne

variable {X : Type} [Group X] [Finite X]

theorem yLifts_inf_centralizer_le_pCore_aux6 {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    {I K : Subgroup X} (hI : I ∈ CY T T₁ T₂)
    (hK : K ≤ Subgroup.centralizer ((⁅gnV T, yLifts T T₁ T₂⁆ : Subgroup X) : Set X))
    (hbar : barO2 I ≤ barO2 K) : False := by
  haveI hVn : (gnV T).Normal := Subgroup.normalClosure_normal
  have hVea := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  have hIC : IsC2 I := by
    obtain ⟨_, _, hL⟩ := hI
    exact hL.1
  have hUD : ⁅I, gnV T⁆ ≤ ⁅gnV T, yLifts T T₁ T₂⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl (le_iSup₂ (f := fun L (_ : L ∈ CY T T₁ T₂) => L) I hI)
  have key : ∀ x ∈ I, Odd (orderOf x) → x ∈ gnC T := by
    intro x hx hodd
    obtain ⟨k, hkK, hkx⟩ := hbar (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 X)) hx)
    have hz : k⁻¹ * x ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hkx
    have hkU : ∀ u ∈ ⁅I, gnV T⁆, k * u = u * k := fun u hu =>
      (Subgroup.mem_centralizer_iff.1 (hK hkK) u (hUD hu)).symm
    have hxU : ∀ s ∈ ⁅I, gnV T⁆, x * s * x⁻¹ ∈ ⁅I, gnV T⁆ := by
      intro s hs
      have hxn : x ∈ Subgroup.normalizer ((⁅I, gnV T⁆ : Subgroup X) : Set X) :=
        mem_normalizer_commutator (liftOf_conj_aux1 (Subgroup.le_normalizer hx))
      exact (Subgroup.mem_normalizer_iff.1 hxn s).1 hs
    have hcong : ∀ s ∈ ⁅I, gnV T⁆, x * s * x⁻¹ = (k⁻¹ * x) * s * (k⁻¹ * x)⁻¹ := by
      intro s hs
      have h1 := hkU _ (hxU s hs)
      calc x * s * x⁻¹ = k⁻¹ * (k * (x * s * x⁻¹)) := by group
        _ = k⁻¹ * ((x * s * x⁻¹) * k) := by rw [h1]
        _ = (k⁻¹ * x) * s * (k⁻¹ * x)⁻¹ := by group
    have hcen := yLifts_inf_centralizer_le_pCore_aux4 hxU hcong hodd
      (pRank_barO2_eq_aux_powTwo hz)
    have hsq := yLifts_inf_centralizer_le_pCore_aux5 hVea (x := x) (fun v hv =>
      hcen _ (Subgroup.commutator_mem_commutator hx hv))
    have hx2 : x ^ 2 ∈ gnC T := by
      rw [gnC, Subgroup.mem_centralizer_iff]
      intro v hv
      have h2 := hsq v hv
      calc v * x ^ 2 = (x ^ 2 * v * (x ^ 2)⁻¹) * x ^ 2 := by rw [h2]
        _ = x ^ 2 * v := by group
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.coprime_two_left.2 hodd)
    rw [← hm]
    exact Subgroup.pow_mem _ hx2 m
  have hIC' : I ≤ gnC T := by
    rw [← hIC.2.1]
    unfold oddHull
    exact (Subgroup.closure_le _).2 fun x hx => key x hx.1 hx.2
  exact (uOf_props hX hI).1 (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hIC')

end StepOne

section Normalizers

variable {X : Type} [Group X] [Finite X]

theorem yLifts_inf_centralizer_le_pCore_aux7 {T T₁ T₂ : Subgroup X} {y : X}
    (hy : y ∈ yLifts T T₁ T₂) :
    y ∈ Subgroup.normalizer ((⁅gnV T, yLifts T T₁ T₂⁆ : Subgroup X) : Set X) := by
  haveI hVn : (gnV T).Normal := Subgroup.normalClosure_normal
  rw [Subgroup.commutator_comm]
  exact mem_normalizer_commutator (liftOf_conj_aux1 (Subgroup.le_normalizer hy))

theorem yLifts_inf_centralizer_le_pCore_aux8c {T T₁ T₂ : Subgroup X} {y k : X}
    (hy : y ∈ yLifts T T₁ T₂)
    (hk : k ∈ Subgroup.centralizer ((⁅gnV T, yLifts T T₁ T₂⁆ : Subgroup X) : Set X)) :
    y * k * y⁻¹ ∈ Subgroup.centralizer ((⁅gnV T, yLifts T T₁ T₂⁆ : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hyn := yLifts_inf_centralizer_le_pCore_aux7 (T₁ := T₁) (T₂ := T₂) hy
  have hd' : y⁻¹ * d * y ∈ (⁅gnV T, yLifts T T₁ T₂⁆ : Subgroup X) :=
    (Subgroup.mem_normalizer_iff''.1 hyn d).1 hd
  have h2 := (Subgroup.mem_centralizer_iff.1 hk) _ hd'
  calc d * (y * k * y⁻¹) = y * ((y⁻¹ * d * y) * k) * y⁻¹ := by group
    _ = y * (k * (y⁻¹ * d * y)) * y⁻¹ := by rw [h2]
    _ = (y * k * y⁻¹) * d := by group

theorem yLifts_inf_centralizer_le_pCore_aux8 {T T₁ T₂ : Subgroup X} {y k : X}
    (hy : y ∈ yLifts T T₁ T₂)
    (hk : k ∈ yLifts T T₁ T₂ ⊓
      Subgroup.centralizer ((⁅gnV T, yLifts T T₁ T₂⁆ : Subgroup X) : Set X)) :
    y * k * y⁻¹ ∈ yLifts T T₁ T₂ ⊓
      Subgroup.centralizer ((⁅gnV T, yLifts T T₁ T₂⁆ : Subgroup X) : Set X) :=
  Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hk.1) (Subgroup.inv_mem _ hy),
    yLifts_inf_centralizer_le_pCore_aux8c hy hk.2⟩

theorem yLifts_inf_centralizer_le_pCore_aux9 {T T₁ T₂ : Subgroup X} (h : IsGNPair T T₁ T₂) {t : X}
    (ht : t ∈ T) : ∀ w ∈ yLifts T T₁ T₂, t * w * t⁻¹ ∈ yLifts T T₁ T₂ := by
  have hle : yLifts T T₁ T₂ ≤ (yLifts T T₁ T₂).comap (MulAut.conj t).toMonoidHom := by
    refine iSup₂_le fun I hI => ?_
    intro i hi
    rw [Subgroup.mem_comap]
    have hmem : conjSub t I ∈ CY T T₁ T₂ := conj_mem_CY h hI ht
    exact le_iSup₂ (f := fun L (_ : L ∈ CY T T₁ T₂) => L) (conjSub t I) hmem
      (Subgroup.mem_map_of_mem _ hi)
  intro w hw
  exact hle hw

end Normalizers

theorem yLifts_inf_centralizer_le_pCore (hKSML3 : KSML3) {X : Type} [Group X] [Finite X]
    {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hg : GNGood T T₁ T₂)
    (hL3 : ∀ (Ls : Subgroup (X ⧸ gnC T)) (L : Subgroup X), GNYComponent T T₁ T₂ Ls →
      LiftOf T L Ls → IsLThreeOfExp 1 ↥Ls) :
    yLifts T T₁ T₂ ⊓ Subgroup.centralizer ((⁅gnV T, yLifts T T₁ T₂⁆ : Subgroup X) : Set X) ≤
      CFSG.pCore 2 X := by
  have _ := hg
  classical
  set K : Subgroup X := yLifts T T₁ T₂ ⊓
    Subgroup.centralizer ((⁅gnV T, yLifts T T₁ T₂⁆ : Subgroup X) : Set X) with hKdef
  have hC2 : ∀ I ∈ CY T T₁ T₂, IsC2 I := by
    rintro I ⟨Ls, -, hL⟩
    exact hL.1
  have hZ : ∀ I ∈ CY T T₁ T₂, Nat.card (Subgroup.center ↥(barO2 I)) = 1 := by
    rintro I ⟨Ls, hLs, hL⟩
    exact (barO2_isLThree_of_lift hKSML3 hX hLs.1 hL (hL3 Ls I hLs hL)).2
  have hIY : ∀ I ∈ CY T T₁ T₂, I ≤ yLifts T T₁ T₂ := fun I hI =>
    le_iSup₂ (f := fun L (_ : L ∈ CY T T₁ T₂) => L) I hI
  have hNI : ∀ I ∈ CY T T₁ T₂, ∀ y ∈ yLifts T T₁ T₂,
      QuotientGroup.mk' (CFSG.pCore 2 X) y ∈
        Subgroup.normalizer ((barO2 I : Subgroup (X ⧸ CFSG.pCore 2 X)) : Set (X ⧸ CFSG.pCore 2 X)) := by
    intro I hI
    have hle : yLifts T T₁ T₂ ≤ (Subgroup.normalizer
        ((barO2 I : Subgroup (X ⧸ CFSG.pCore 2 X)) : Set (X ⧸ CFSG.pCore 2 X))).comap
          (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
      refine iSup₂_le fun J hJ => ?_
      intro j hj
      rw [Subgroup.mem_comap]
      by_cases hIJ : J = I
      · subst hIJ
        exact Subgroup.le_normalizer (Subgroup.mem_map_of_mem _ hj)
      · have hcomm := isC2_commute_of_ne (hC2 J hJ) (hC2 I hI) hIJ
        have hj' : QuotientGroup.mk' (CFSG.pCore 2 X) j ∈
            Subgroup.centralizer ((barO2 I : Subgroup (X ⧸ CFSG.pCore 2 X)) :
              Set (X ⧸ CFSG.pCore 2 X)) := by
          have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
            (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 X)) hj)
          exact h1
        exact (Subgroup.centralizer_le_normalizer _) hj'
    intro y hy
    exact hle hy
  have hinf : ∀ I ∈ CY T T₁ T₂, barO2 I ⊓ barO2 K = ⊥ := by
    intro I hI
    refine yLifts_inf_centralizer_le_pCore_aux2 (hC2 I hI).component.2.2 (hZ I hI) ?_ ?_
    · rw [Subgroup.le_normalizer_iff]
      rintro _ ⟨l, hl, rfl⟩ _ ⟨k, hk, rfl⟩
      refine ⟨l * k * l⁻¹, yLifts_inf_centralizer_le_pCore_aux8 (hIY I hI hl) hk, ?_⟩
      simp
    · intro hle
      exact yLifts_inf_centralizer_le_pCore_aux6 hX hI inf_le_right hle
  have hcommK : ∀ I ∈ CY T T₁ T₂, ∀ k ∈ K, ∀ l ∈ I,
      QuotientGroup.mk' (CFSG.pCore 2 X) k * QuotientGroup.mk' (CFSG.pCore 2 X) l =
        QuotientGroup.mk' (CFSG.pCore 2 X) l * QuotientGroup.mk' (CFSG.pCore 2 X) k := by
    intro I hI k hk l hl
    have hlY := hIY I hI hl
    have hkY : k ∈ yLifts T T₁ T₂ := hk.1
    have h1 : ⁅QuotientGroup.mk' (CFSG.pCore 2 X) k, QuotientGroup.mk' (CFSG.pCore 2 X) l⁆ ∈
        barO2 I := by
      have h2 := (Subgroup.mem_normalizer_iff.1 (hNI I hI k hkY)
        (QuotientGroup.mk' (CFSG.pCore 2 X) l)).1 (Subgroup.mem_map_of_mem _ hl)
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ (Subgroup.mem_map_of_mem _ hl))
    have h3 : ⁅QuotientGroup.mk' (CFSG.pCore 2 X) k, QuotientGroup.mk' (CFSG.pCore 2 X) l⁆ ∈
        barO2 K := by
      have h4 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 X))
        (Subgroup.mul_mem K hk (yLifts_inf_centralizer_le_pCore_aux8 hlY (K.inv_mem hk)))
      rw [commutatorElement_def]
      simpa [mul_assoc] using h4
    have h5 : ⁅QuotientGroup.mk' (CFSG.pCore 2 X) k, QuotientGroup.mk' (CFSG.pCore 2 X) l⁆ ∈
        barO2 I ⊓ barO2 K := Subgroup.mem_inf.2 ⟨h1, h3⟩
    rw [hinf I hI, Subgroup.mem_bot] at h5
    exact commutatorElement_eq_one_iff_mul_comm.1 h5
  have hfin : (CY T T₁ T₂).Finite := Set.toFinite _
  have hYle : yLifts T T₁ T₂ ≤ (⨆ i ∈ hfin.toFinset, barO2 i).comap
      (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    refine iSup₂_le fun I hI => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    exact le_iSup₂ (f := fun i (_ : i ∈ hfin.toFinset) => barO2 i) I
      (hfin.mem_toFinset.2 hI) (Subgroup.mem_map_of_mem _ hx)
  intro k hk
  rw [← QuotientGroup.eq_one_iff]
  refine yLifts_inf_centralizer_le_pCore_aux1 barO2 hfin.toFinset ?_ ?_
    (z := QuotientGroup.mk' (CFSG.pCore 2 X) k) (hYle hk.1) ?_
  · intro i hi a ha hcomm
    have hi' := hfin.mem_toFinset.1 hi
    have hz : (⟨a, ha⟩ : ↥(barO2 i)) ∈ Subgroup.center ↥(barO2 i) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2).symm
    rw [Subgroup.eq_bot_of_card_eq _ (hZ i hi'), Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  · intro i hi j hj hne a ha b hb
    have hc := isC2_commute_of_ne (hC2 i (hfin.mem_toFinset.1 hi))
      (hC2 j (hfin.mem_toFinset.1 hj)) hne
    have ha' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc ha
    exact ((Subgroup.mem_centralizer_iff.1 ha') b hb).symm
  · intro i hi a ha
    obtain ⟨l, hl, rfl⟩ := ha
    exact hcommK i (hfin.mem_toFinset.1 hi) k hk l hl

section WSub

variable {G : Type} [Group G] [Finite G]

theorem yLifts_le_normalizer_wSub_aux1 (M T : Subgroup G) (U : Subgroup ↥M) {A : Subgroup G}
    (g : G) (hA : A = (U.map M.subtype).map (MulAut.conj g).toMonoidHom) (hAT : A ≤ T) :
    A ≤ wSub G M T U := by
  unfold wSub
  exact le_iSup₂ (f := fun A (_ : A ∈ {A : Subgroup G |
    (∃ g : G, A = (U.map M.subtype).map (MulAut.conj g).toMonoidHom) ∧ A ≤ T}) => A) A
    ⟨⟨g, hA⟩, hAT⟩

theorem yLifts_le_normalizer_wSub_gen (hKSML3 : KSML3) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hgn : GNSetting ↥M (T.subgroupOf M)) (hpair : IsGNPair (T.subgroupOf M) T₁ T₂)
    (hgood : GNGood (T.subgroupOf M) T₁ T₂) (h25 : Row1525 G M T T₁ T₂) {U : Subgroup ↥M}
    (hW4 : wSub G M T U ≤ (Subgroup.centralizer
      ((⁅gnV (T.subgroupOf M), yLifts (T.subgroupOf M) T₁ T₂⁆ : Subgroup ↥M) :
        Set ↥M)).map M.subtype) :
    (yLifts (T.subgroupOf M) T₁ T₂).map M.subtype ≤
      Subgroup.normalizer ((wSub G M T U : Subgroup G) : Set G) := by
  have key : ∀ y ∈ (yLifts (T.subgroupOf M) T₁ T₂).map M.subtype, ∀ x ∈ wSub G M T U, x ∈ T →
      y * x * y⁻¹ ∈ T := by
    intro y hy x hxW hxT
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 (hW4 hxW)
    have hx'T : x' ∈ T.subgroupOf M := hxT
    have hcY : y' * x' * y'⁻¹ * x'⁻¹ ∈ yLifts (T.subgroupOf M) T₁ T₂ := by
      have h1 := yLifts_inf_centralizer_le_pCore_aux9 hpair hx'T y'⁻¹
        (Subgroup.inv_mem _ hy')
      have h2 := Subgroup.mul_mem _ hy' h1
      simpa [mul_assoc] using h2
    have hcC : y' * x' * y'⁻¹ * x'⁻¹ ∈ Subgroup.centralizer
        ((⁅gnV (T.subgroupOf M), yLifts (T.subgroupOf M) T₁ T₂⁆ : Subgroup ↥M) : Set ↥M) :=
      Subgroup.mul_mem _ (yLifts_inf_centralizer_le_pCore_aux8c hy' hx') (Subgroup.inv_mem _ hx')
    have hc := yLifts_inf_centralizer_le_pCore hKSML3 hgn hgood h25.2
      (Subgroup.mem_inf.2 ⟨hcY, hcC⟩)
    have hcT : y' * x' * y'⁻¹ * x'⁻¹ ∈ T.subgroupOf M := pCore_le_gnC_aux1 hgn.sylow hc
    have h3 : y' * x' * y'⁻¹ ∈ T.subgroupOf M := by
      have h4 := Subgroup.mul_mem _ hcT hx'T
      simpa using h4
    exact h3
  intro y hy
  rw [mem_normalizer_iff_map_conj_eq]
  have hconj : (wSub G M T U).map (MulAut.conj y).toMonoidHom ≤ wSub G M T U := by
    rw [Subgroup.map_le_iff_le_comap]
    unfold wSub
    refine iSup₂_le fun A hA => ?_
    obtain ⟨⟨g, hAg⟩, hAT⟩ := hA
    have hAW : A ≤ wSub G M T U := yLifts_le_normalizer_wSub_aux1 M T U g hAg hAT
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_iSup₂_of_le (A.map (MulAut.conj y).toMonoidHom) ⟨⟨y * g, ?_⟩, ?_⟩ le_rfl
    · rw [hAg, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    · rintro _ ⟨a, ha, rfl⟩
      exact key y hy a (hAW ha) (hAT ha)
  exact Subgroup.eq_of_le_of_card_ge hconj
    (Subgroup.card_map_of_injective (MulAut.conj y).injective).ge

end WSub

end CFSG.LocalAnalysis.RankThreeUC.S15
