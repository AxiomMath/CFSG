module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Comm
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Sylow

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem conj_mem_centralizer {V : Subgroup G} {g c : G} (hg : g ∈ normalizer (V : Set G))
    (hc : c ∈ centralizer (V : Set G)) : g * c * g⁻¹ ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := (mem_normalizer_iff''.1 hg v).1 hv
  have h := hc _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * v := by group

theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    normalizer (V : Set G) ≤ normalizer ((centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_iff.2 fun c => ⟨fun hc => conj_mem_centralizer hg hc, fun hc => ?_⟩
  have := conj_mem_centralizer (inv_mem hg) hc
  simpa [mul_assoc] using this

section Alpha

variable {V : Subgroup G} {Ws : Subgroup (MulAut ↥V)}

theorem alpha_conj {g h : G} (hgV : g ∈ normalizer (V : Set G)) (hhV : h ∈ normalizer (V : Set G))
    (hgW : actFun V g ∈ normalizer (Ws : Set (MulAut ↥V)))
    (hhW : actFun V h ∈ normalizer (Ws : Set (MulAut ↥V))) :
    actFun Ws (actFun V (g * h * g⁻¹)) =
      actFun Ws (actFun V g) * actFun Ws (actFun V h) * (actFun Ws (actFun V g))⁻¹ := by
  rw [actFun_conj V hgV hhV, actFun_conj Ws hgW hhW]

theorem alpha_mul {g h : G} (hgV : g ∈ normalizer (V : Set G)) (hhV : h ∈ normalizer (V : Set G))
    (hgW : actFun V g ∈ normalizer (Ws : Set (MulAut ↥V)))
    (hhW : actFun V h ∈ normalizer (Ws : Set (MulAut ↥V))) :
    actFun Ws (actFun V (g * h)) = actFun Ws (actFun V g) * actFun Ws (actFun V h) := by
  rw [actFun_mul V hgV hhV, actFun_mul Ws hgW hhW]

theorem alpha_inv {g : G} (hgV : g ∈ normalizer (V : Set G))
    (hgW : actFun V g ∈ normalizer (Ws : Set (MulAut ↥V))) :
    actFun Ws (actFun V g⁻¹) = (actFun Ws (actFun V g))⁻¹ := by
  rw [actFun_inv V hgV, actFun_inv Ws hgW]

theorem exists_conj_alpha_eq {I S : Subgroup G} {t : G} {IA AS : Set (MulAut ↥Ws)}
    (hI : ∀ g ∈ I, g ∈ normalizer (V : Set G) ∧ actFun V g ∈ normalizer (Ws : Set (MulAut ↥V)))
    (hSI : S ≤ I) (htS : t ∈ S) (hIA : ∀ g ∈ I, actFun Ws (actFun V g) ∈ IA)
    (hAS : ∀ s ∈ S, actFun Ws (actFun V s) ∈ AS)
    (hAS' : ∀ σ ∈ AS, ∃ s ∈ S, σ = actFun Ws (actFun V s))
    (hP3 : {x | x ∈ AS ∧ ∃ i ∈ IA, x = i * actFun Ws (actFun V t) * i⁻¹} =
      {x | ∃ s ∈ AS, x = s * actFun Ws (actFun V t) * s⁻¹})
    (h620 : ∀ h ∈ normalizer (V : Set G), h * t * h⁻¹ ∈ I → h ∈ I)
    {x : G} (hxS : x ∈ S) (hx : ∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = x) :
    ∃ s₁ ∈ S, actFun Ws (actFun V (s₁⁻¹ * x * s₁)) = actFun Ws (actFun V t) := by
  obtain ⟨h, hhN, rfl⟩ := hx
  have htI : t ∈ I := hSI htS
  have hhI : h ∈ I := h620 h hhN (hSI hxS)
  have h1 : actFun Ws (actFun V (h * t * h⁻¹)) =
      actFun Ws (actFun V h) * actFun Ws (actFun V t) * (actFun Ws (actFun V h))⁻¹ :=
    alpha_conj hhN (hI t htI).1 (hI h hhI).2 (hI t htI).2
  have h2 : actFun Ws (actFun V (h * t * h⁻¹)) ∈
      {x | x ∈ AS ∧ ∃ i ∈ IA, x = i * actFun Ws (actFun V t) * i⁻¹} :=
    ⟨hAS _ hxS, actFun Ws (actFun V h), hIA h hhI, h1⟩
  rw [hP3] at h2
  obtain ⟨σ, hσ, hσx⟩ := h2
  obtain ⟨s₁, hs₁, rfl⟩ := hAS' σ hσ
  refine ⟨s₁, hs₁, ?_⟩
  have hs₁I : s₁ ∈ I := hSI hs₁
  have hxI : h * t * h⁻¹ ∈ I := hSI hxS
  have h3 : actFun Ws (actFun V (s₁⁻¹ * (h * t * h⁻¹) * s₁)) =
      (actFun Ws (actFun V s₁))⁻¹ * actFun Ws (actFun V (h * t * h⁻¹)) * actFun Ws (actFun V s₁) := by
    have h4 := alpha_conj (V := V) (Ws := Ws) (inv_mem (hI s₁ hs₁I).1) (hI _ hxI).1
      (by rw [actFun_inv V (hI s₁ hs₁I).1]; exact inv_mem (hI s₁ hs₁I).2) (hI _ hxI).2
    rw [inv_inv] at h4
    rw [h4, actFun_inv V (hI s₁ hs₁I).1, actFun_inv Ws (hI s₁ hs₁I).2, inv_inv]
  rw [h3, hσx]
  group

theorem exists_conj_of_alpha_eq [Finite G] {I S : Subgroup G} {t : G}
    (hI : ∀ g ∈ I, g ∈ normalizer (V : Set G) ∧ actFun V g ∈ normalizer (Ws : Set (MulAut ↥V)))
    (hSI : S ≤ I) (htS : t ∈ S) (ht2 : t * t = 1) (hS2 : IsPGroup 2 S)
    (hSH : fusionIsSylowIn 2 S (normalizer (V : Set G)))
    (hWab : IsElemAbelian 2 Ws)
    (hWcard : Nat.card Ws = Nat.card ↥(Ws ⊓ centralizer ({actFun V t} : Set (MulAut ↥V))) *
      Nat.card ↥(Ws ⊓ centralizer ({actFun V t} : Set (MulAut ↥V))))
    (hWsyl : fusionIsSylowIn 2 Ws
      (centralizer (Ws : Set (MulAut ↥V)) ⊓ imgIn V (normalizer (V : Set G))))
    (hWS : Ws ≤ imgIn V S)
    (hTrans : ∀ S₀ : Subgroup G, fusionIsSylowIn 2 S₀ (centralizer (V : Set G)) →
      (∀ s ∈ S₀, t * s * t⁻¹ ∈ S₀) →
      ∀ a ∈ {x : G | (∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = x) ∧ ∃ s ∈ S₀, x = s * t},
      ∀ b ∈ {x : G | (∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = x) ∧ ∃ s ∈ S₀, x = s * t},
        ∃ s ∈ S₀, s * a * s⁻¹ = b)
    {x : G} (hxS : x ∈ S) (hx : ∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = x)
    (halpha : actFun Ws (actFun V x) = actFun Ws (actFun V t)) :
    ∃ s ∈ S, s * t * s⁻¹ = x := by
  have htI : t ∈ I := hSI htS
  have htN : t ∈ normalizer (V : Set G) := (hI t htI).1
  have hτW : actFun V t ∈ normalizer (Ws : Set (MulAut ↥V)) := (hI t htI).2
  have hτ2 : actFun V t * actFun V t = 1 := by
    rw [← actFun_mul V htN htN, ht2, actFun_one]
  have hxI : x ∈ I := hSI hxS
  have hxN := (hI x hxI).1
  have hxW := (hI x hxI).2
  have hx2 : x * x = 1 := by
    obtain ⟨h, -, rfl⟩ := hx
    calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  set c : G := x * t⁻¹ with hc
  have hcS : c ∈ S := mul_mem hxS (inv_mem htS)
  have hcI : c ∈ I := hSI hcS
  have hcN : c ∈ normalizer (V : Set G) := (hI c hcI).1
  have hcW : actFun V c ∈ normalizer (Ws : Set (MulAut ↥V)) := (hI c hcI).2
  have hxc : x = c * t := by rw [hc]; group
  have halc : actFun Ws (actFun V c) = 1 := by
    have h1 : actFun Ws (actFun V c) =
        actFun Ws (actFun V x) * (actFun Ws (actFun V t))⁻¹ := by
      rw [hc, alpha_mul hxN (inv_mem htN) hxW
        (by rw [actFun_inv V htN]; exact inv_mem hτW), alpha_inv htN hτW]
    rw [h1, halpha, mul_inv_cancel]
  have hcC : actFun V c ∈ centralizer (Ws : Set (MulAut ↥V)) :=
    (actFun_eq_one_iff Ws hcW).1 halc
  have hcH : actFun V c ∈ imgIn V (normalizer (V : Set G)) := actFun_mem_imgIn hcN hcN
  have hc2 : IsPGroup 2 (zpowers (actFun V c)) :=
    IsPGroup.to_le (isPGroup_imgIn V hS2) (zpowers_le.2 (actFun_mem_imgIn hcS hcN))
  have hwW : actFun V c ∈ Ws :=
    mem_of_isPGroup_of_central_sylow hWsyl
      (fun c' hc' a ha => (Subgroup.mem_centralizer_iff.1 hc'.1 a ha).symm) ⟨hcC, hcH⟩ hc2
  set w : MulAut ↥V := actFun V c with hw
  have h2 : t * c * t = c⁻¹ := by
    have h3 : c * (t * c * t) = 1 := by
      calc c * (t * c * t) = c * t * (c * t) := by group
        _ = 1 := by rw [← hxc]; exact hx2
    exact eq_inv_of_mul_eq_one_right h3
  have h4 : actFun V t * w * actFun V t = w⁻¹ := by
    have h5 := congrArg (actFun V) h2
    rw [actFun_mul V (mul_mem htN hcN) htN, actFun_mul V htN hcN, actFun_inv V hcN] at h5
    exact h5
  have hw2 : w * w = 1 := by simpa [sq] using hWab.2 w hwW
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have h5 : actFun V t * w = w * actFun V t := by
    calc actFun V t * w = actFun V t * w * (actFun V t * actFun V t) := by rw [hτ2, mul_one]
      _ = (actFun V t * w * actFun V t) * actFun V t := by group
      _ = w * actFun V t := by rw [h4, hwi]
  obtain ⟨u, huW, hwu⟩ := exists_comm_eq_of_card hWab hτW hτ2 hWcard hwW h5
  obtain ⟨a', ha'S, ha'N, ha'u⟩ := (mem_imgIn_iff V S).1 (hWS huW)
  set k : G := a' * t * a'⁻¹ * t⁻¹ with hk
  have hkS : k ∈ S := mul_mem (mul_mem (mul_mem ha'S htS) (inv_mem ha'S)) (inv_mem htS)
  have hkN : k ∈ normalizer (V : Set G) := (hI k (hSI hkS)).1
  have hkstar : actFun V k = w := by
    have e1 : actFun V (a' * t * a'⁻¹) = actFun V a' * actFun V t * (actFun V a')⁻¹ :=
      actFun_conj V ha'N htN
    rw [hk, actFun_mul V (mul_mem (mul_mem ha'N htN) (inv_mem ha'N)) (inv_mem htN), e1,
      actFun_inv V htN, ha'u]
    exact hwu.symm
  set c' : G := k⁻¹ * c with hc'
  have hc'S : c' ∈ S := mul_mem (inv_mem hkS) hcS
  have hc'N : c' ∈ normalizer (V : Set G) := (hI c' (hSI hc'S)).1
  have hc'one : actFun V c' = 1 := by
    rw [hc', actFun_mul V (inv_mem hkN) hcN, actFun_inv V hkN, hkstar, inv_mul_cancel]
  have hc'C : c' ∈ centralizer (V : Set G) := (actFun_eq_one_iff V hc'N).1 hc'one
  have hc''S : t⁻¹ * c' * t ∈ S := mul_mem (mul_mem (inv_mem htS) hc'S) htS
  have hc''C : t⁻¹ * c' * t ∈ centralizer (V : Set G) := by
    simpa using conj_mem_centralizer (inv_mem htN) hc'C
  set c₃ : G := a'⁻¹ * (t⁻¹ * c' * t) * a' with hc₃
  have hc₃S : c₃ ∈ S := mul_mem (mul_mem (inv_mem ha'S) hc''S) ha'S
  have hc₃C : c₃ ∈ centralizer (V : Set G) := by
    simpa using conj_mem_centralizer (inv_mem ha'N) hc''C
  set s₀ : G := t * c₃ * t⁻¹ with hs₀
  have hs₀S : s₀ ∈ S := mul_mem (mul_mem htS hc₃S) (inv_mem htS)
  have hs₀C : s₀ ∈ centralizer (V : Set G) := conj_mem_centralizer htN hc₃C
  set y : G := a'⁻¹ * x * a' with hy
  have hxk : x = k * c' * t := by
    calc x = c * t := hxc
      _ = k * (k⁻¹ * c) * t := by group
      _ = k * c' * t := by rw [hc']
  have hyeq : y = s₀ * t := by
    rw [hy, hxk, hk, hs₀, hc₃]
    group
  have hS₀ : fusionIsSylowIn 2 (S ⊓ centralizer (V : Set G)) (centralizer (V : Set G)) :=
    fusionIsSylowIn_inf_of_normal hSH (Subgroup.centralizer_le_normalizer _)
      (normalizer_le_normalizer_centralizer V)
  have hinv : ∀ s ∈ S ⊓ centralizer (V : Set G), t * s * t⁻¹ ∈ S ⊓ centralizer (V : Set G) :=
    fun s hs => by
      rw [Subgroup.mem_inf] at hs ⊢
      exact ⟨mul_mem (mul_mem htS hs.1) (inv_mem htS), conj_mem_centralizer htN hs.2⟩
  have hyO : y ∈ {z : G | (∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = z) ∧
      ∃ s ∈ S ⊓ centralizer (V : Set G), z = s * t} := by
    refine ⟨?_, ⟨s₀, ⟨hs₀S, hs₀C⟩, hyeq⟩⟩
    obtain ⟨h, hhN, hhx⟩ := hx
    refine ⟨a'⁻¹ * h, mul_mem (inv_mem ha'N) hhN, ?_⟩
    rw [hy, ← hhx]
    group
  have htO : t ∈ {z : G | (∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = z) ∧
      ∃ s ∈ S ⊓ centralizer (V : Set G), z = s * t} :=
    ⟨⟨1, one_mem _, by simp⟩, ⟨1, one_mem _, by simp⟩⟩
  obtain ⟨s₂, hs₂, hs₂y⟩ := hTrans _ hS₀ hinv t htO y hyO
  refine ⟨a' * s₂, mul_mem ha'S hs₂.1, ?_⟩
  have hxy : x = a' * y * a'⁻¹ := by rw [hy]; group
  rw [hxy, ← hs₂y]
  group

end Alpha

theorem exists_conj_of_mem_conj_normalizer [Finite G] {V : Subgroup G} {Ws : Subgroup (MulAut ↥V)}
    {I S : Subgroup G} {t : G} {IA AS : Set (MulAut ↥Ws)}
    (hI : ∀ g ∈ I, g ∈ normalizer (V : Set G) ∧ actFun V g ∈ normalizer (Ws : Set (MulAut ↥V)))
    (hSI : S ≤ I) (htS : t ∈ S) (ht2 : t * t = 1) (hS2 : IsPGroup 2 S)
    (hSH : fusionIsSylowIn 2 S (normalizer (V : Set G)))
    (hIA : ∀ g ∈ I, actFun Ws (actFun V g) ∈ IA)
    (hAS : ∀ s ∈ S, actFun Ws (actFun V s) ∈ AS)
    (hAS' : ∀ σ ∈ AS, ∃ s ∈ S, σ = actFun Ws (actFun V s))
    (hP3 : {x | x ∈ AS ∧ ∃ i ∈ IA, x = i * actFun Ws (actFun V t) * i⁻¹} =
      {x | ∃ s ∈ AS, x = s * actFun Ws (actFun V t) * s⁻¹})
    (h620 : ∀ h ∈ normalizer (V : Set G), h * t * h⁻¹ ∈ I → h ∈ I)
    (hWab : IsElemAbelian 2 Ws)
    (hWcard : Nat.card Ws = Nat.card ↥(Ws ⊓ centralizer ({actFun V t} : Set (MulAut ↥V))) *
      Nat.card ↥(Ws ⊓ centralizer ({actFun V t} : Set (MulAut ↥V))))
    (hWsyl : fusionIsSylowIn 2 Ws
      (centralizer (Ws : Set (MulAut ↥V)) ⊓ imgIn V (normalizer (V : Set G))))
    (hWS : Ws ≤ imgIn V S)
    (hTrans : ∀ S₀ : Subgroup G, fusionIsSylowIn 2 S₀ (centralizer (V : Set G)) →
      (∀ s ∈ S₀, t * s * t⁻¹ ∈ S₀) →
      ∀ a ∈ {x : G | (∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = x) ∧ ∃ s ∈ S₀, x = s * t},
      ∀ b ∈ {x : G | (∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = x) ∧ ∃ s ∈ S₀, x = s * t},
        ∃ s ∈ S₀, s * a * s⁻¹ = b)
    {x : G} (hxS : x ∈ S) (hx : ∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = x) :
    ∃ s ∈ S, s * t * s⁻¹ = x := by
  obtain ⟨s₁, hs₁, hα⟩ := exists_conj_alpha_eq hI hSI htS hIA hAS hAS' hP3 h620 hxS hx
  have hx₁S : s₁⁻¹ * x * s₁ ∈ S := mul_mem (mul_mem (inv_mem hs₁) hxS) hs₁
  have hx₁ : ∃ h ∈ normalizer (V : Set G), h * t * h⁻¹ = s₁⁻¹ * x * s₁ := by
    obtain ⟨h, hh, rfl⟩ := hx
    exact ⟨s₁⁻¹ * h, mul_mem (inv_mem (hI s₁ (hSI hs₁)).1) hh, by group⟩
  obtain ⟨s, hs, hsx⟩ := exists_conj_of_alpha_eq hI hSI htS ht2 hS2 hSH hWab hWcard hWsyl hWS hTrans
    hx₁S hx₁ hα
  refine ⟨s₁ * s, mul_mem hs₁ hs, ?_⟩
  calc s₁ * s * t * (s₁ * s)⁻¹ = s₁ * (s * t * s⁻¹) * s₁⁻¹ := by group
    _ = s₁ * (s₁⁻¹ * x * s₁) * s₁⁻¹ := by rw [hsx]
    _ = x := by group

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
