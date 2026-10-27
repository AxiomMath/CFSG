module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.ChevThree
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixLevi
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFiveAux
public import CFSG.LocalAnalysis.AGLEmbedding.ZOneFacts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.AGLEmbedding
  CFSG.Open CFSG.QuasithinUnique

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem mem_of_map_mem_of_central_inf (f : G →* G') {L S₀ : Subgroup G} (hS₀ : S₀ ≤ L)
    (hS2 : IsPGroup 2 S₀) (hc : ∀ k ∈ L, f k = 1 → ∀ l ∈ L, k * l = l * k)
    (h2 : ∀ k ∈ L, f k = 1 → ∀ n : ℕ, k ^ 2 ^ n = 1 → k = 1) {a : G} (haL : a ∈ L) {m : ℕ}
    (ha : a ^ 2 ^ m = 1) (hfa : f a ∈ S₀.map f) : a ∈ S₀ := by
  obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.1 hfa
  obtain ⟨n, hn⟩ := hS2 ⟨s, hs⟩
  have hn' : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hkL : s⁻¹ * a ∈ L := L.mul_mem (L.inv_mem (hS₀ hs)) haL
  have hk : f (s⁻¹ * a) = 1 := by rw [map_mul, map_inv, hsa, inv_mul_cancel]
  have hsk : s⁻¹ * a * s = s * (s⁻¹ * a) := hc _ hkL hk s (hS₀ hs)
  have hcomm : Commute s⁻¹ a := by
    have e1 : s * a = a * s := by
      calc s * a = s * (s⁻¹ * a * s) := by rw [hsk]; group
        _ = a * s := by group
    exact (Commute.inv_left e1)
  have hpow : (s⁻¹ * a) ^ 2 ^ (n + m) = 1 := by
    rw [hcomm.mul_pow, inv_pow, pow_add, pow_mul, hn', one_pow, inv_one, one_mul, mul_comm,
      pow_mul, ha, one_pow]
  have h1 := h2 _ hkL hk _ hpow
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact hs

theorem inf_normalizer_map_eq_of_central (f : G →* G') {L S₀ : Subgroup G} (hS₀ : S₀ ≤ L)
    (hS2 : IsPGroup 2 S₀) (hc : ∀ k ∈ L, f k = 1 → ∀ l ∈ L, k * l = l * k)
    (h2 : ∀ k ∈ L, f k = 1 → ∀ n : ℕ, k ^ 2 ^ n = 1 → k = 1) :
    L.map f ⊓ Subgroup.normalizer ((S₀.map f : Subgroup G') : Set G') =
      (L ⊓ Subgroup.normalizer (S₀ : Set G)).map f := by
  apply le_antisymm
  · rintro y ⟨⟨l, hl, rfl⟩, hy⟩
    have key : ∀ r ∈ L, f r ∈ Subgroup.normalizer ((S₀.map f : Subgroup G') : Set G') →
        ∀ x ∈ S₀, r * x * r⁻¹ ∈ S₀ := by
      intro r hr hfr x hx
      obtain ⟨n, hn⟩ := hS2 ⟨x, hx⟩
      have hn' : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      refine mem_of_map_mem_of_central_inf f hS₀ hS2 hc h2
        (L.mul_mem (L.mul_mem hr (hS₀ hx)) (L.inv_mem hr)) (m := n) ?_ ?_
      · rw [conj_pow, hn', mul_one, mul_inv_cancel]
      · rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.1 hfr _).1 ⟨x, hx, rfl⟩
    refine ⟨l, ⟨hl, Quasithin.B6.mem_normalizer_of_forall_mem (key l hl hy) fun x hx => ?_⟩, rfl⟩
    have hy' : f l⁻¹ ∈ Subgroup.normalizer ((S₀.map f : Subgroup G') : Set G') := by
      rw [map_inv]
      exact inv_mem hy
    simpa using key l⁻¹ (L.inv_mem hl) hy' x hx
  · refine (Subgroup.map_inf_le _ _ _).trans (inf_le_inf_left _ ?_)
    exact Subgroup.le_normalizer_map f

theorem isMinOverBorel_map_of_central (f : G →* G') {L S₀ P : Subgroup G} (hS₀ : S₀ ≤ L)
    (hS2 : IsPGroup 2 S₀) (hc : ∀ k ∈ L, f k = 1 → ∀ l ∈ L, k * l = l * k)
    (h2 : ∀ k ∈ L, f k = 1 → ∀ n : ℕ, k ^ 2 ^ n = 1 → k = 1) (hP : IsMinOverBorel L S₀ P) :
    IsMinOverBorel (L.map f) (S₀.map f) (P.map f) := by
  obtain ⟨hPL, hlt, hmin⟩ := hP
  have hB := inf_normalizer_map_eq_of_central f hS₀ hS2 hc h2
  set B := L ⊓ Subgroup.normalizer (S₀ : Set G) with hBdef
  have hKB : ∀ k ∈ L, f k = 1 → k ∈ B := by
    intro k hk hfk
    refine ⟨hk, Subgroup.centralizer_le_normalizer (S₀ : Set G) ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hc k hk hfk s (hS₀ hs)).symm
  have hpull : ∀ x ∈ L, f x ∈ B.map f → x ∈ B := by
    intro x hx hfx
    obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.1 hfx
    have hbB : b⁻¹ * x ∈ B := hKB _ (L.mul_mem (L.inv_mem hb.1) hx)
      (by rw [map_mul, map_inv, hbx, inv_mul_cancel])
    have e : x = b * (b⁻¹ * x) := by group
    rw [e]
    exact B.mul_mem hb hbB
  refine ⟨Subgroup.map_mono hPL, ?_, ?_⟩
  · rw [hB]
    refine lt_of_le_of_ne (Subgroup.map_mono hlt.le) fun heq => hlt.not_ge fun x hx => ?_
    refine hpull x (hPL hx) ?_
    rw [heq]
    exact ⟨x, hx, rfl⟩
  · intro Q hQ1 hQ2
    rw [hB] at hQ1 ⊢
    have hBQ : B ≤ Q.comap f ⊓ P := fun b hb => ⟨hQ1 ⟨b, hb, rfl⟩, hlt.le hb⟩
    have hQeq : (Q.comap f ⊓ P).map f = Q := by
      apply le_antisymm
      · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le f Q)
      · intro q hq
        obtain ⟨x, hx, rfl⟩ := hQ2 hq
        exact ⟨x, ⟨hq, hx⟩, rfl⟩
    rcases hmin _ hBQ inf_le_right with h | h
    · left
      rw [← hQeq, h]
    · right
      rw [← hQeq, h]

end Transport

section Lift

variable {X : Type} [Group X] [Finite X]

theorem exists_mem_lift_of_dvd_center (hG : KFactChevGenCentre) {T T₁ T₂ L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hY : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (hcl : IsClassicalTwoOrG2 (↥Ls ⧸ Subgroup.center ↥Ls))
    (hcov : ParabolicCover T T₁ T₂ Ls) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpZ : p ∣ Nat.card (Subgroup.center ↥(barO2 L))) :
    ∃ l ∈ L, orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) l) = p ∧
      QuotientGroup.mk' (CFSG.pCore 2 X) l ∉ (Subgroup.center ↥(barO2 L)).map (barO2 L).subtype ∧
      toStar T l ∈ gnA T T₁ Ls := by
  set ψ := QuotientGroup.mk' (CFSG.pCore 2 X) with hψ
  let φ' : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
    QuotientGroup.map (CFSG.pCore 2 X) (gnC T) (MonoidHom.id X)
      (by rw [Subgroup.comap_id]; exact pCore_le_gnC hX)
  have hφψ : φ'.comp ψ = toStar T := MonoidHom.ext fun _ => rfl
  have hmap : ∀ A : Subgroup X, (A.map ψ).map φ' = A.map (toStar T) := fun A => by
    rw [Subgroup.map_map, hφψ]
  have hmapL : (barO2 L).map φ' = Ls := (hmap L).trans hL.2
  have hcen := (liftOf_central_ext hX hY.1 hL).1
  have hkZ : ∀ k ∈ barO2 L, φ' k = 1 →
      k ∈ (Subgroup.center ↥(barO2 L)).map (barO2 L).subtype := by
    rintro _ ⟨a, ha, rfl⟩ hk
    exact hcen ⟨a, ⟨ha, (QuotientGroup.eq_one_iff a).1 hk⟩, rfl⟩
  have hc : ∀ k ∈ barO2 L, φ' k = 1 → ∀ l ∈ barO2 L, k * l = l * k := by
    intro k hk hk1 l hl
    obtain ⟨z, hz, rfl⟩ := hkZ k hk hk1
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩)).symm
  have hodd := centre_barO2_odd hL.1
  have h2 : ∀ k ∈ barO2 L, φ' k = 1 → ∀ n : ℕ, k ^ 2 ^ n = 1 → k = 1 := by
    intro k hk hk1 n hn
    obtain ⟨z, hz, rfl⟩ := hkZ k hk hk1
    set w : Subgroup.center ↥(barO2 L) := ⟨z, hz⟩ with hw
    have hwn : w ^ 2 ^ n = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [hw] using hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hwn)
    have hj0 : j = 0 := by
      by_contra hj0
      have h3 : 2 ∣ 2 ^ j := dvd_pow_self 2 hj0
      have h4 := Nat.odd_iff.1 (hodd.of_dvd_nat (hj ▸ orderOf_dvd_natCard w))
      omega
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    have h5 := congrArg
      (fun v : Subgroup.center ↥(barO2 L) => ((v : ↥(barO2 L)) : X ⧸ CFSG.pCore 2 X)) hj
    simpa [hw] using h5
  have hT : IsSylowTwoOf (T.map ψ) ⊤ := by
    have h := AscEightFive.isSylowTwoOf_map hX.sylow ψ
    rwa [Subgroup.map_top_of_surjective ψ (QuotientGroup.mk'_surjective _)] at h
  set S₀ := T.map ψ ⊓ barO2 L with hS₀def
  have hS₀ : IsSylowTwoOf S₀ (barO2 L) :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' hL.1.component.2.1 hT
  have hS₀map : S₀.map φ' = gnImg T T ⊓ Ls := by
    have h1 := AscEightFive.isSylowTwoOf_map hS₀ φ'
    rw [hmapL] at h1
    have h3 : S₀.map φ' ≤ gnImg T T ⊓ Ls := by
      refine (Subgroup.map_inf_le _ _ _).trans ?_
      rw [hmap T, hmapL]
      exact le_rfl
    exact (CFSG.AGLEmbedding.isSylowTwoOf_eq_of_le h1 inf_le_right
      ((hX.sylow.2.1.map (QuotientGroup.mk' (gnC T))).to_le inf_le_left) h3).symm
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hY.1 hL
  have hcl' : IsClassicalTwoOrG2 (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) := by
    rcases hcl with ⟨d, hd, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨d, hd, ⟨e'⟩⟩
    · exact Or.inl ⟨d, hd, ⟨eQ.trans e'⟩⟩
    · exact Or.inr (Or.inl ⟨n, hn, ⟨eQ.trans e'⟩⟩)
    · exact Or.inr (Or.inr ⟨d, hd, ⟨eQ.trans e'⟩⟩)
  obtain ⟨Ps, hPs, hgen, hK⟩ := hG _ (barO2 L) S₀ hL.1.component.2.2 hcl' hS₀
  set Ps' : Set (Subgroup (X ⧸ gnC T)) := (fun P => P.map φ') '' Ps with hPs'def
  have hPs' : ∀ P ∈ Ps', IsMinOverBorel Ls (gnImg T T ⊓ Ls) P := by
    rintro _ ⟨P, hP, rfl⟩
    have h := isMinOverBorel_map_of_central φ' hS₀.1 hS₀.2.1 hc h2 (hPs P hP)
    rwa [hmapL, hS₀map] at h
  have hgen' : Ls = ⨆ P ∈ Ps', pElementSubgroup 2 P := by
    apply le_antisymm
    · calc Ls = (barO2 L).map φ' := hmapL.symm
        _ = (⨆ P ∈ Ps, pElementSubgroup 2 P).map φ' := by rw [← hgen]
        _ ≤ ⨆ P ∈ Ps', pElementSubgroup 2 P := by
          rw [Subgroup.map_iSup]
          refine iSup_le fun P => ?_
          rw [Subgroup.map_iSup]
          refine iSup_le fun hP => ?_
          exact (K517Six.map_pElementSubgroup_le φ' P).trans
            (le_iSup₂ (f := fun (Q : Subgroup (X ⧸ gnC T)) (_ : Q ∈ Ps') =>
              pElementSubgroup 2 Q) (P.map φ') ⟨P, hP, rfl⟩)
    · exact iSup₂_le fun P hP => (pElementSubgroup_le P).trans (hPs' P hP).1
  obtain ⟨⟨_, ⟨P, hP, rfl⟩, hP₁⟩, -⟩ := exists_parabolic_le_gnA hY hcov hPs' hgen'
  obtain ⟨x, hx, hxo, hxZ⟩ := hK P hP p hp hp2 hpZ
  obtain ⟨l, hl, rfl⟩ := (pElementSubgroup_le P).trans (hPs P hP).1 hx
  exact ⟨l, hl, hxo, hxZ, hP₁ (K517Six.map_pElementSubgroup_le φ' P ⟨_, hx, rfl⟩)⟩

end Lift

end CFSG.LocalAnalysis.RankThreeUC.S15
