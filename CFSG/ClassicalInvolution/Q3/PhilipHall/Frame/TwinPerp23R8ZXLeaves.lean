module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6M
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZXWAux
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZXE
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6MLab
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoY
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoRho
import CFSG.ClassicalInvolution.Sp62Rec.SylowOfHat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Sp62Rec CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki



variable {n : ℕ}

theorem p23E8ZXW_proved (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n) (hα : P23Alpha n)
    (hCE : P23E8ZCE n) : P23E8ZXW n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZs hAE Z hIZ _ hOe T A hTB hT512 _ _ huniq
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hzt : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hzt hc.std.hK'
  have hK0 : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  set E := rLayer (Om R) e
  set B := Z ⊔ E
  have hCB : Subgroup.centralizer ({e} : Set Y) ≤ B :=
    p23E8Z_centralizer_e_le hT hTwo hα hCE hcit hP Y R S t K' W u e g hc hno hZs hAE Z hIZ
  have hOC := Z6M.oddC_eq_bot hT hTwo hα hcit hP hc hno hZs hAE
  have hOCt : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    TwinConnT.oddCoreIn_eq_bot_of_classicalOddCore hOC
  have hinj := Z6M.piC_injective hOC
  have hcentJ : ∀ J ∈ tqMembers3 (Om R) e, J ≤ Subgroup.centralizer ({e} : Set Y) := fun J hJ =>
    le_centralizer_of_oddCoreIn_eq_bot hJ.2 (oddCoreIn_eq_bot_of_mem_Om hc.std.perp hOCt hJ.1)
  have hKe := hcentJ _ (ZTwo.twins_tq hc).1
  have hK'e := hcentJ _ (ZTwo.twins_tq hc).2
  have hKE : tightCore R ≤ E := (le_rLayer_iff_le_centralizer hc.std.perp hd.he2 hK0).mpr hKe
  have hK'E : K' ≤ E :=
    (le_rLayer_iff_le_centralizer hc.std.perp hd.he2 hc.std.hK'.1).mpr hK'e
  have hLE : ∀ L : Subgroup Y, (L = tightCore R ∨ L = K') → L ≤ E := by
    rintro L (rfl | rfl)
    · exact hKE
    · exact hK'E
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (ZTwo.e_comm_t hc)
  have hZcu := R56.p23_zstar_cu hT hc hZs
  have hMe : ∀ s : Y, (∀ k ∈ tightCore R, s * k = k * s) → (∀ k ∈ K', s * k = k * s) →
      s * e = e * s := by
    intro s hsK hsK'
    have hsC : s ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hsK t hzt.mem)
    have h1 := p23MBar_proved hcit hP Y R S t K' W u e g hc hZcu ⟨e, heC⟩ rfl
      (F7I.piC _ ⟨s, hsC⟩) (Z6M.piC_comm_of_comm (m := ⟨s, hsC⟩) hsK)
      (Z6M.piC_comm_of_comm (m := ⟨s, hsC⟩) hsK')
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hinj h1)
  have hconjM : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ s : Y,
      (∀ k ∈ tightCore R, s * k = k * s) → (∀ k ∈ K', s * k = k * s) →
      (∀ k ∈ tightCore R, c⁻¹ * s * c * k = k * (c⁻¹ * s * c)) ∧
        (∀ k ∈ K', c⁻¹ * s * c * k = k * (c⁻¹ * s * c)) := by
    intro c hcC s hsK hsK'
    have hsL : ∀ x : Y, (x ∈ tightCore R ∨ x ∈ K') → s * x = x * s := by
      rintro x (hx | hx)
      · exact hsK x hx
      · exact hsK' x hx
    have hmem : ∀ (H : Subgroup Y) (x : Y), x ∈ H → c * x * c⁻¹ ∈ conjSub c H := by
      intro H x hx
      rw [mem_conjSub_iff]
      have e1 : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      rw [e1]
      exact hx
    have key : ∀ x : Y, (c * x * c⁻¹ ∈ tightCore R ∨ c * x * c⁻¹ ∈ K') →
        c⁻¹ * s * c * x = x * (c⁻¹ * s * c) := by
      intro x hx
      have h1 := hsL _ hx
      calc c⁻¹ * s * c * x = c⁻¹ * (s * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * s) * c := by rw [h1]
        _ = x * (c⁻¹ * s * c) := by group
    rcases p23_conj_twins hc hcC with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun k hk => key k (Or.inl (h1 ▸ hmem _ k hk)),
        fun k hk => key k (Or.inr (h2 ▸ hmem _ k hk))⟩
    · exact ⟨fun k hk => key k (Or.inr (h1 ▸ hmem _ k hk)),
        fun k hk => key k (Or.inl (h2 ▸ hmem _ k hk))⟩
  set M : Subgroup Y := Subgroup.centralizer ((tightCore R : Set Y) ∪ (K' : Set Y))
  have hmemM : ∀ s, s ∈ M ↔ (∀ k ∈ tightCore R, s * k = k * s) ∧ (∀ k ∈ K', s * k = k * s) := by
    intro s
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨fun k hk => (h k (Or.inl hk)).symm, fun k hk => (h k (Or.inr hk)).symm⟩
    · rintro ⟨h1, h2⟩ k (hk | hk)
      · exact (h1 k hk).symm
      · exact (h2 k hk).symm
  have htM : t ∈ M := (hmemM t).mpr
    ⟨fun k hk =>
      (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hzt hk)).symm,
      fun k hk =>
        (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz' hk)).symm⟩
  have heM : e ∈ M := (hmemM e).mpr
    ⟨fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp (hKe hk)).symm,
      fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp (hK'e hk)).symm⟩
  set G : Subgroup Y := Subgroup.centralizer ({t} : Set Y)
  set C : Subgroup Y := Subgroup.centralizer (M : Set Y)
  have hGM : ∀ g ∈ G, ∀ m ∈ M, g⁻¹ * m * g ∈ M := fun g hg m hm => by
    obtain ⟨h1, h2⟩ := hconjM g hg m ((hmemM m).mp hm).1 ((hmemM m).mp hm).2
    exact (hmemM _).mpr ⟨h1, h2⟩
  have hCG : C ≤ G := fun c hcC => by
    rw [Subgroup.mem_centralizer_iff] at hcC
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcC t htM).symm
  have hCe : C ≤ Subgroup.centralizer ({e} : Set Y) := fun c hcC => by
    rw [Subgroup.mem_centralizer_iff] at hcC
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcC e heM).symm
  have hGC : ∀ g ∈ G, ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun g hg c hcC => by
    rw [Subgroup.mem_centralizer_iff] at hcC ⊢
    intro m hm
    have h1 := hcC _ (hGM g hg m hm)
    calc m * (g * c * g⁻¹) = g * ((g⁻¹ * m * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * m * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * m := by group
  have hnorm : ∀ g ∈ G, conjSub g C = C := fun g hg => by
    apply le_antisymm
    · rintro _ ⟨c, hcC, rfl⟩
      exact hGC g hg c hcC
    · intro c hcC
      rw [mem_conjSub_iff]
      have := hGC g⁻¹ (G.inv_mem hg) c hcC
      simpa using this
  have hCeG : ∀ c ∈ C, ∀ g ∈ G, c * (g * e * g⁻¹) = g * e * g⁻¹ * c := by
    intro c hcC g hg
    have h1 : g * e * g⁻¹ ∈ M := by
      have := hGM g⁻¹ (G.inv_mem hg) e heM
      simpa using this
    rw [Subgroup.mem_centralizer_iff] at hcC
    exact (hcC _ h1).symm
  obtain ⟨J, J', hJ, hJ', hne, hzJ, hzJ', hcomm⟩ := hIZ.twin
  obtain ⟨f, Θ, φ, D, β, hβ, b₀, hlab, hlab'⟩ :=
    Z6M.i1_action_lab_final hc.std.perp hAE hIZ hJ hJ' hne hzJ hzJ' hcomm
  rw [coreAt_eq_of_le_centralizer hJ.1 (hcentJ J hJ)] at hlab
  rw [coreAt_eq_of_le_centralizer hJ'.1 (hcentJ J' hJ')] at hlab'
  have hpair := twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne
  have hJpair : J = tightCore R ∨ J = K' := by
    have h1 : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
      ⟨hJ.1, t, hzt, hzJ⟩
    rw [hpair] at h1
    simpa using h1
  have hJ'pair : J' = tightCore R ∨ J' = K' := by
    have h1 : J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
      ⟨hJ'.1, t, hzt, hzJ'⟩
    rw [hpair] at h1
    simpa using h1
  have hlabK : ∀ L : Subgroup Y, (L = tightCore R ∨ L = K') →
      ∃ c : Bool, (L.subgroupOf E).map f = memAt β hβ c := by
    intro L hL
    have hLJ : L = J ∨ L = J' := by
      rcases hL with rfl | rfl <;> rcases hJpair with h | h <;> rcases hJ'pair with h' | h'
      all_goals first
        | exact Or.inl h.symm
        | exact Or.inr h'.symm
        | exact absurd (h'.trans h.symm) hne
    rcases hLJ with rfl | rfl
    · exact ⟨b₀, hlab⟩
    · exact ⟨!b₀, hlab'⟩
  have hsurjK : ∀ c : Bool, ∃ L : Subgroup Y, (L = tightCore R ∨ L = K') ∧
      (L.subgroupOf E).map f = memAt β hβ c := by
    intro c
    by_cases hcb : c = b₀
    · exact ⟨J, hJpair, hcb ▸ hlab⟩
    · have : c = !b₀ := (by decide : ∀ a b : Bool, a ≠ b → a = !b) c b₀ hcb
      exact ⟨J', hJ'pair, this ▸ hlab'⟩
  have hOE : oddCoreIn E = ⊥ := D.oddCoreIn_eq_bot hOe
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, D.φ_ker, hOE, Subgroup.bot_subgroupOf]
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, D.f_ker, hOE, Subgroup.bot_subgroupOf]
  let F : ↥B ≃* ↥Sp62Rec.I1.Wsub := (MulEquiv.ofBijective φ ⟨hφinj, D.φ_surj⟩).trans Θ.symm
  have hFf : ∀ (x : Y) (hx : x ∈ E),
      ((F ⟨x, D.E_le_B hx⟩ : ↥Sp62Rec.I1.Wsub) : Wr 6) = f ⟨x, hx⟩ := by
    intro x hx
    obtain ⟨hm, h1⟩ := D.φ_f x hx
    show ((Θ.symm (φ ⟨x, D.E_le_B hx⟩) : ↥Sp62Rec.I1.Wsub) : Wr 6) = _
    rw [h1, MulEquiv.symm_apply_apply]
  have hFmem : ∀ L : Subgroup Y, (hL : L ≤ E) → ∀ c : Bool,
      (L.subgroupOf E).map f = memAt β hβ c →
      ∀ (l : Y) (hl : l ∈ L), ((F ⟨l, D.E_le_B (hL hl)⟩ : ↥Sp62Rec.I1.Wsub) : Wr 6) ∈
        memAt β hβ c := by
    intro L hL c hLc l hl
    rw [hFf l (hL hl), ← hLc]
    exact ⟨⟨l, hL hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hFsurj : ∀ L : Subgroup Y, L ≤ E → ∀ c : Bool,
      (L.subgroupOf E).map f = memAt β hβ c →
      ∀ k ∈ memAt β hβ c, ∃ l ∈ L, ∃ hlB : l ∈ B,
        ((F ⟨l, hlB⟩ : ↥Sp62Rec.I1.Wsub) : Wr 6) = k := by
    intro L hL c hLc k hk
    rw [← hLc] at hk
    obtain ⟨⟨l, hlE⟩, hl, rfl⟩ := hk
    exact ⟨l, Subgroup.mem_subgroupOf.mp hl, D.E_le_B hlE, hFf l hlE⟩
  set AC : Subgroup Y := (((ZXW.aHat β hβ).subgroupOf Sp62Rec.I1.Wsub).comap
    F.toMonoidHom).map B.subtype
  have hmemAC : ∀ a : Y, a ∈ AC ↔
      ∃ ha : a ∈ B, ((F ⟨a, ha⟩ : ↥Sp62Rec.I1.Wsub) : Wr 6) ∈ ZXW.aHat β hβ := by
    intro a
    constructor
    · rintro ⟨⟨a', ha'B⟩, ha', rfl⟩
      exact ⟨ha'B, ha'⟩
    · rintro ⟨ha, h⟩
      exact ⟨⟨a, ha⟩, h, rfl⟩
  have hAC64 : IsE64 AC := by
    have h1 : IsE64 ((ZXW.aHat β hβ).subgroupOf Sp62Rec.I1.Wsub) :=
      isE64_comap_of_injective Sp62Rec.I1.Wsub.subtype_injective (ZXW.isE64_aHat β hβ)
        (by rw [Subgroup.range_subtype]; exact ZXW.aHat_le_Wsub β hβ)
    have h2 : IsE64 (((ZXW.aHat β hβ).subgroupOf Sp62Rec.I1.Wsub).comap F.toMonoidHom) :=
      isE64_comap_of_injective F.injective h1 (fun x _ => ⟨F.symm x, F.apply_symm_apply x⟩)
    exact isE64_map_of_injective B.subtype_injective h2
  have hKN : ∀ L : Subgroup Y, (L = tightCore R ∨ L = K') →
      L ≤ Subgroup.normalizer (AC : Set Y) := by
    intro L hL l hl
    obtain ⟨c, hLc⟩ := hlabK L hL
    have hconjAC : ∀ l ∈ L, ∀ a ∈ AC, l * a * l⁻¹ ∈ AC := by
      intro l hl a ha
      obtain ⟨haB, haF⟩ := (hmemAC a).mp ha
      have hlB : l ∈ B := D.E_le_B (hLE L hL hl)
      refine (hmemAC _).mpr ⟨B.mul_mem (B.mul_mem hlB haB) (B.inv_mem hlB), ?_⟩
      have h1 : F ⟨l * a * l⁻¹, B.mul_mem (B.mul_mem hlB haB) (B.inv_mem hlB)⟩ =
          F ⟨l, hlB⟩ * F ⟨a, haB⟩ * (F ⟨l, hlB⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact ZXW.conj_mem_aHat β hβ (hFmem L (hLE L hL) c hLc l hl) haF
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact hconjAC l hl a
    · intro ha
      have := hconjAC l⁻¹ (L.inv_mem hl) _ ha
      simpa [mul_assoc] using this
  have hMB : ∀ m ∈ M, m ∈ B := fun m hm => hCB (Subgroup.mem_centralizer_singleton_iff.mpr
    (hMe m ((hmemM m).mp hm).1 ((hmemM m).mp hm).2))
  have hFM : ∀ (m : Y) (hm : m ∈ M),
      ((F ⟨m, hMB m hm⟩ : ↥Sp62Rec.I1.Wsub) : Wr 6) ∈ ZXW.aHat β hβ := by
    intro m hm
    refine ZXW.mem_aHat_of_comm β hβ (F ⟨m, hMB m hm⟩).2 fun c k hk => ?_
    obtain ⟨L, hL, hLc⟩ := hsurjK c
    obtain ⟨l, hlL, hlB, rfl⟩ := hFsurj L (hLE L hL) c hLc k hk
    have hml : m * l = l * m := by
      rcases hL with rfl | rfl
      · exact ((hmemM m).mp hm).1 l hlL
      · exact ((hmemM m).mp hm).2 l hlL
    have h1 : (⟨m, hMB m hm⟩ : ↥B) * ⟨l, hlB⟩ = ⟨l, hlB⟩ * ⟨m, hMB m hm⟩ := Subtype.ext hml
    have h2 := congrArg (fun z : ↥B => ((F z : ↥Sp62Rec.I1.Wsub) : Wr 6)) h1
    simpa only [map_mul, Subgroup.coe_mul] using h2
  have hACC : AC ≤ C := by
    intro a ha
    obtain ⟨haB, haF⟩ := (hmemAC a).mp ha
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := (ZXW.isE64_aHat β hβ).1 _ haF _ (hFM m hm)
    have h2 : F (⟨m, hMB m hm⟩ * ⟨a, haB⟩) = F (⟨a, haB⟩ * ⟨m, hMB m hm⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h1.symm
    exact congrArg Subtype.val (F.injective h2)
  obtain ⟨T₀, hT₀B, -, hT₀t⟩ := p23E8ZSix_of_ce hT hTwo hα hCE hcit hP Y R S t K' W u e g hc hno
    hZs hAE Z hIZ hOCt
  have hP₀ : IsSylow2In (T₀ : Subgroup Y) G :=
    ⟨fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hT₀t x hx).symm, T₀.isPGroup',
      fun _ _ hV'2 hle => T₀.is_maximal' hV'2 hle⟩
  have hP₀e : (T₀ : Subgroup Y) ≤ Subgroup.centralizer ({e} : Set Y) := hT₀B.trans D.B_le
  obtain ⟨c', hc'C, -, hne', -⟩ := ZTwo.exists_y hT hcit hP hTwo hα hc hno hZs hAE
  have hBcard : Nat.card B = 23040 := Z6M.I1Action.card_B D hOE
  have hTS : IsSylow2In T B := ZX.isSylow2In_of_card_512 hBcard hTB
    (IsPGroup.of_card (n := 9) (by rw [hT512]; norm_num)) hT512
  obtain ⟨x, hxG, hxe, hxodd, hxA, b, -, hbA⟩ := ZXW.frattini_step hCG hnorm
    (hCe.trans hCB) hCeG hTS huniq hAC64 hACC hP₀ hP₀e hc'C hne'
  obtain ⟨hxK, hxK'⟩ := ZXW.fix_of_odd hxodd (Ne.symm hc.std.hne) (p23_conj_twins hc hxG)
  obtain ⟨L, hL, hxL, hnL⟩ : ∃ L : Subgroup Y, (L = tightCore R ∨ L = K') ∧ conjSub x L = L ∧
      ¬ ∀ k ∈ L, x * k = k * x := by
    by_cases h1 : ∀ k ∈ tightCore R, x * k = k * x
    · by_cases h2 : ∀ k ∈ K', x * k = k * x
      · exact absurd (hMe x h1 h2) hxe
      · exact ⟨K', Or.inr rfl, hxK', h2⟩
    · exact ⟨tightCore R, Or.inl rfl, hxK, h1⟩
  have hL8 : Nat.card L = 8 := by
    obtain ⟨c, hLc⟩ := hlabK L hL
    have h1 : Nat.card ((L.subgroupOf E).map f) = Nat.card (L.subgroupOf E) :=
      Subgroup.card_map_of_injective hfinj
    rw [hLc, natCard_memAt] at h1
    rw [h1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hLE L hL)).toEquiv).symm
  have hx'L : conjSub (b * x * b⁻¹) (conjSub b L) = conjSub b L := by
    rw [← conjSub_mul, show b * x * b⁻¹ * b = b * x by group, conjSub_mul, hxL]
  refine ⟨b * x * b⁻¹, ?_, conjSub b L, ?_, ?_, hx'L, ?_⟩
  · apply ZXW.mem_normalizer_of_conjSub_eq
    rw [← hbA, ← conjSub_mul, show b * x * b⁻¹ * b = b * x by group, conjSub_mul, hxA]
  · rcases hL with rfl | rfl
    · exact conjInvariant_conjClass (tightCore R) b _ hK0
    · exact conjInvariant_conjClass (tightCore R) b _ hc.std.hK'.1
  · rw [← hbA]
    exact ZX.conjSub_le_normalizer (hKN L hL) b
  · intro U hUL hUc hU4 hxU
    apply hnL
    have hx'odd : Odd (orderOf (b * x * b⁻¹)) := by
      rw [show b * x * b⁻¹ = (MulAut.conj b).toMonoidHom x from rfl,
        orderOf_injective _ (MulAut.conj b).injective]
      exact hxodd
    have hK''8 : Nat.card (conjSub b L) = 8 := by
      rw [← hL8]
      exact Subgroup.card_map_of_injective (MulAut.conj b).injective
    have hcomm' := ZXW.comm_of_odd_of_conj_eq hK''8 hUL hUc hU4 hx'odd hx'L hxU
    intro k hk
    have h1 := hcomm' (b * k * b⁻¹) (conj_mem_conjSub hk)
    have h2 : b * (x * k) * b⁻¹ = b * (k * x) * b⁻¹ := by
      calc b * (x * k) * b⁻¹ = b * x * b⁻¹ * (b * k * b⁻¹) := by group
        _ = b * k * b⁻¹ * (b * x * b⁻¹) := h1
        _ = b * (k * x) * b⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem p23E8ZXStrong_of_W
    (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n) (hα : P23Alpha n)
    (hN : P23E8ZNormT n) (hCE : P23E8ZCE n) (hME : P23E8ZXE n) : P23E8ZXStrong n :=
  p23E8ZXStrong_of_leaves hE hT hα hN (p23E8ZXW_proved hT hTwo hα hCE) hME

theorem p23E8ZXStrong_proved
    (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n) (hα : P23Alpha n)
    (hN : P23E8ZNormT n) (hCE : P23E8ZCE n) : P23E8ZXStrong n :=
  p23E8ZXStrong_of_W hE hT hTwo hα hN hCE (p23E8ZXE_proved hE hT hα hN)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
