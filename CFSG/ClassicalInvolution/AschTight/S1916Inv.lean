module

public import CFSG.ClassicalInvolution.AschTight.Hall196Idx2
public import CFSG.ClassicalInvolution.AschTight.S1916Sec

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.GorensteinWalter
open scoped commutatorElement MatrixGroups

theorem exists_involution_of_isSylow2In_inf {Γ : Type} [Group Γ] [Finite Γ] {N₀ E : Subgroup Γ}
    [hN₀ : N₀.Normal] (hE2 : IsPGroup 2 E) (hD : IsSylow2In (E ⊓ N₀) N₀) {ι : Γ}
    (hι : ι ∈ N₀ ⊔ E) (hιN : ι ∉ N₀) (hι2 : ι * ι = 1) : ∃ e ∈ E, e ∉ N₀ ∧ e * e = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEN : E ≤ Subgroup.normalizer (N₀ : Set Γ) := fun x _ =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hN₀.conj_mem y hy x, fun hy => by
      have := hN₀.conj_mem _ hy x⁻¹
      simpa [mul_assoc] using this⟩
  obtain ⟨V, hV, hEV⟩ := IsSylow2In.exists_ge hE2 (le_sup_right : E ≤ N₀ ⊔ E)
  have hVN : V ⊓ N₀ = E ⊓ N₀ := by
    refine (hD.2.2 (V ⊓ N₀) inf_le_right (hV.2.1.to_le inf_le_left)
      (inf_le_inf_right _ hEV))
  have hVN' : V ≤ Subgroup.normalizer (N₀ : Set Γ) := fun x _ =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hN₀.conj_mem y hy x, fun hy => by
      have := hN₀.conj_mem _ hy x⁻¹
      simpa [mul_assoc] using this⟩
  have h1 := card_sup_mul_card_inf hEN
  have h2 := card_sup_mul_card_inf hVN'
  have h3 : Nat.card ↥(N₀ ⊔ V) ≤ Nat.card ↥(N₀ ⊔ E) :=
    Subgroup.card_le_of_le (sup_le le_sup_left hV.1)
  rw [inf_comm N₀ V, hVN, inf_comm] at h2
  have hpos : 0 < Nat.card ↥(N₀ ⊓ E) := Nat.card_pos
  have hpos' : 0 < Nat.card N₀ := Nat.card_pos
  have hVE : Nat.card V ≤ Nat.card E := by
    have h4 : Nat.card N₀ * Nat.card V ≤ Nat.card N₀ * Nat.card E := by
      rw [← h1, ← h2]
      exact Nat.mul_le_mul_right _ h3
    exact Nat.le_of_mul_le_mul_left h4 hpos'
  have hES : IsSylow2In E (N₀ ⊔ E) := hV.of_natCard_le hE2 le_sup_right hVE
  have hι1 : ι ≠ 1 := fun h => hιN (h ▸ N₀.one_mem)
  have hι2' : IsPGroup 2 ↥(Subgroup.zpowers ι) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hι2) hι1, pow_one])
  obtain ⟨P₁, hP₁, hιP₁⟩ := IsSylow2In.exists_ge hι2' (Subgroup.zpowers_le.mpr hι)
  obtain ⟨h, -, hh⟩ := IsSylow2In.exists_conj hP₁ hES
  refine ⟨h * ι * h⁻¹, hh ▸ conj_mem_conjSub (hιP₁ (Subgroup.mem_zpowers ι)), fun hc => hιN ?_,
    ?_⟩
  · have := hN₀.conj_mem _ hc h⁻¹
    simpa [mul_assoc] using this
  · calc h * ι * h⁻¹ * (h * ι * h⁻¹) = h * (ι * ι) * h⁻¹ := by group
      _ = 1 := by rw [hι2]; group

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

theorem psi_eq_one_iff (e : ↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f)))
    (h3 : 3 < Nat.card (GaloisField p f)) (n : Subgroup.normalizer (K : Set G)) :
    normalizerToPGammaL2Mod e hFcard hF h3 n = 1 ↔ (n : G) ∈ centralizerModOdd ⊤ K := by
  rw [Hall196.normalizerToPGammaL2Mod_eq_one_iff]
  exact ⟨fun h => ⟨Subgroup.mem_top _, n.2, mem_normalizer_oddCoreOf_of_mem_normalizer n.2, h⟩,
    fun h => h.2.2.2⟩

theorem psi_mem_iff [IsSimpleGroup G] (hd : Sec19Data p f K z S W)
    (e : ↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f)))
    (h3 : 3 < Nat.card (GaloisField p f)) (n : Subgroup.normalizer (K : Set G)) :
    normalizerToPGammaL2Mod e hFcard hF h3 n ∈ pGammaL2PGLRange (GaloisField p f) ↔
      (n : G) ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  set Ψ := normalizerToPGammaL2Mod e hFcard hF h3 with hΨ
  rw [← Hall196.map_sec19X_eq_pGammaL2PGLRange hd e hFcard hF h3]
  constructor
  · rintro ⟨x, hxX, hx⟩
    have hy : Ψ (x⁻¹ * n) = 1 := by rw [map_mul, map_inv, hx, inv_mul_cancel]
    have hyC := (psi_eq_one_iff e hFcard hF h3 _).mp hy
    have e1 : (n : G) = (x : G) * ((x⁻¹ * n : Subgroup.normalizer (K : Set G)) : G) := by simp
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hxX))
      (Subgroup.mem_sup_right hyC)
  · intro hn
    set H₀ : Subgroup G := (((sec19X K z).subgroupOf (Subgroup.normalizer (K : Set G))).map
      Ψ).comap Ψ |>.map (Subgroup.normalizer (K : Set G)).subtype with hH₀
    have hNC := sd_normalizer_eq hd
    have hle : sec19X K z ⊔ centralizerModOdd ⊤ K ≤ H₀ := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · have hxN : x ∈ Subgroup.normalizer (K : Set G) := hNC.ge (sec19X_le_centralizer K z hx)
        refine ⟨⟨x, hxN⟩, ?_, rfl⟩
        exact ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      · have hxN : x ∈ Subgroup.normalizer (K : Set G) := hx.2.1
        refine ⟨⟨x, hxN⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, (psi_eq_one_iff e hFcard hF h3 _).mpr hx]
        exact Subgroup.one_mem _
    obtain ⟨n', hn', hn'n⟩ := hle hn
    have : n' = n := Subtype.ext hn'n
    rw [← this]
    exact hn'

theorem exists_sq_mem_cStar [IsSimpleGroup G] (hd : Sec19Data p f K z S W)
    (hS : ¬ (S : Subgroup G) ≤ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ s ∈ (S : Subgroup G), s ∉ sec19X K z ⊔ centralizerModOdd ⊤ K ∧
      s * s ∈ centralizerModOdd ⊤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hd.tight
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD ht
  have : Finite (PGammaL2 (GaloisField p f)) := Hall196.finite_pGammaL2
  have hNC := sd_normalizer_eq hd
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := hd.hSz.trans hNC.ge
  set Ψ := normalizerToPGammaL2Mod e hFcard hF h3 with hΨ
  set E := ((S : Subgroup G).subgroupOf (Subgroup.normalizer (K : Set G))).map Ψ with hE
  have hE2 : IsPGroup 2 E := (S.isPGroup'.comap_subtype).map Ψ
  have hXN : sec19X K z ≤ Subgroup.normalizer (K : Set G) :=
    (sec19X_le_centralizer K z).trans hNC.ge
  have hSX : IsSylow2In ((S : Subgroup G) ⊓ sec19X K z) (sec19X K z) :=
    isSylow2In_inf S hd.hSz (sec19X_le_centralizer K z) fun c hc =>
      mem_normalizer_iff_conjSub_eq.mpr (conjSub_sec19X K hc)
  have hSX' := Hall196.isSylow2In_map_hom Ψ (Hall196.isSylow2In_subgroupOf_of_le hSX hXN)
  rw [Hall196.map_sec19X_eq_pGammaL2PGLRange hd e hFcard hF h3] at hSX'
  have hSXE : (((S : Subgroup G) ⊓ sec19X K z).subgroupOf
      (Subgroup.normalizer (K : Set G))).map Ψ ≤ E ⊓ pGammaL2PGLRange (GaloisField p f) :=
    le_inf (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp hx).1) hSX'.1
  have hD : IsSylow2In (E ⊓ pGammaL2PGLRange (GaloisField p f))
      (pGammaL2PGLRange (GaloisField p f)) :=
    hSX'.of_natCard_le (hE2.to_le inf_le_left) inf_le_right (Subgroup.card_le_of_le hSXE)
  obtain ⟨b, hbS, hbT⟩ := Set.not_subset.mp hS
  set b' : Subgroup.normalizer (K : Set G) := ⟨b, hSN hbS⟩ with hb'
  have hb'E : Ψ b' ∈ E := ⟨b', Subgroup.mem_subgroupOf.mpr hbS, rfl⟩
  have hb'L : Ψ b' ∉ pGammaL2PGLRange (GaloisField p f) := fun h =>
    hbT ((psi_mem_iff hd e hFcard hF h3 b').mp h)
  set σ₀ := SemidirectProduct.rightHom (Ψ b') with hσ₀
  have hσ₀1 : σ₀ ≠ 1 := by
    intro h
    apply hb'L
    change Ψ b' ∈ (SemidirectProduct.inl : PGL2 (GaloisField p f) →*
      PGammaL2 (GaloisField p f)).range
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact h
  obtain ⟨k, hk⟩ := hE2 ⟨Ψ b', hb'E⟩
  have hσ₀ord : orderOf σ₀ ∣ 2 ^ k := by
    have h1 : orderOf (Ψ b') ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk (Ψ b') hb'E]
      exact orderOf_dvd_of_pow_eq_one hk
    exact (orderOf_map_dvd _ _).trans h1
  obtain ⟨j, hj, hσj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hσ₀ord
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hσ₀1 (orderOf_eq_one_iff.mp (by simpa using hσj))
  have h2dvd : 2 ∣ orderOf σ₀ := by
    rw [hσj]
    exact dvd_pow_self 2 hj0
  set β := Ψ b' ^ (orderOf σ₀ / 2) with hβ
  set σ := σ₀ ^ (orderOf σ₀ / 2) with hσ
  have hσord : orderOf σ = 2 :=
    orderOf_pow_orderOf_div (by rw [hσj]; positivity) h2dvd
  have hβσ : SemidirectProduct.rightHom β = σ := by rw [hβ, map_pow]
  set ι : PGammaL2 (GaloisField p f) := SemidirectProduct.inr σ with hι
  have hσ2 : σ * σ = 1 := by rw [← _root_.sq, ← hσord, pow_orderOf_eq_one]
  have hι2 : ι * ι = 1 := by rw [hι, ← map_mul, hσ2, map_one]
  have hιL : ι ∉ pGammaL2PGLRange (GaloisField p f) := by
    intro h
    change ι ∈ (SemidirectProduct.inl : PGL2 (GaloisField p f) →*
      PGammaL2 (GaloisField p f)).range at h
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, hι,
      SemidirectProduct.rightHom_inr] at h
    rw [h, orderOf_one] at hσord
    omega
  have hιmem : ι ∈ pGammaL2PGLRange (GaloisField p f) ⊔ E := by
    have hβE : β ∈ E := E.pow_mem hb'E _
    have e1 : ι = (SemidirectProduct.inl β.left)⁻¹ * β := by
      calc ι = SemidirectProduct.inr β.right := by
            rw [hι, ← hβσ, SemidirectProduct.rightHom_eq_right]
        _ = (SemidirectProduct.inl β.left)⁻¹ *
            (SemidirectProduct.inl β.left * SemidirectProduct.inr β.right) := by group
        _ = (SemidirectProduct.inl β.left)⁻¹ * β := by
            rw [SemidirectProduct.inl_left_mul_inr_right]
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ ⟨β.left, rfl⟩))
      (Subgroup.mem_sup_right hβE)
  obtain ⟨e', he'E, he'L, he'2⟩ := exists_involution_of_isSylow2In_inf hE2 hD hιmem hιL hι2
  obtain ⟨n, hnS, hn⟩ := he'E
  refine ⟨n, Subgroup.mem_subgroupOf.mp hnS, fun h => he'L ?_, ?_⟩
  · rw [← hn]
    exact (psi_mem_iff hd e hFcard hF h3 n).mpr h
  · have h1 : Ψ (n * n) = 1 := by rw [map_mul, hn, he'2]
    exact (psi_eq_one_iff e hFcard hF h3 (n * n)).mp h1

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
